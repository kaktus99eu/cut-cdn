import asyncio
import httpx
import aiofiles
import hashlib
import random
import string
import re
from colorama import init, Fore, Style
from rapidfuzz import fuzz
import time
import logging
from bs4 import BeautifulSoup
import difflib
from urllib.parse import urlparse
import json
from datetime import datetime

# ========== CONFIG ==========
URLS_FILE = 'urls.txt'
HEADERS_FILE = 'headers.txt'
RESULT_FILE = 'results.txt'
LENGTH_THRESHOLD = 50
COMMON_VALUE = "h3ll0w0rld"
INITIAL_BATCH = 100
MAX_RETRIES = 1
MAX_CONCURRENT_URLS = 50  # Parallel hosts
MAX_CONCURRENT_BATCHES = 10  # Parallel batch searches per host
# Calibration settings
CALIBRATION_ATTEMPTS = 5
SIMILARITY_THRESHOLD = 0.92  # Lowered to be more sensitive
# Enhanced analysis settings
DOM_SIMILARITY_WEIGHT = 0.5
LENGTH_SIMILARITY_WEIGHT = 0.2
STATUS_SIMILARITY_WEIGHT = 0.3
STRUCTURAL_THRESHOLD = 0.85  # Threshold for structural similarity

# Enhanced dynamic content patterns
DYNAMIC_IGNORE_PATTERNS = [
    # Reference numbers and timestamps
    r'Reference&#32;&#35;[\w\.]+',
    r'https?&#58;&#47;&#47;[\w\.]+&#47;[\w\.]+',
    # Common timestamp formats
    r'\b\d{10,}\b',
    # CSRF tokens
    r'<input type="hidden" name="csrf_token" value="[^"]+">',
    r'__token__=\w+',
    # Session identifiers
    r'PHPSESSID=\w+',
    r'session=\w+',
    r'sessionid=\w+',
    # Cache busters and nonces
    r'\b(cb|nonce|ts|timestamp|_t|_rand)=[\w-]+\b',
    # Dynamic IDs and hashes
    r'\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b',  # UUID
    r'\b[0-9a-f]{32}\b',  # MD5
    r'\b[0-9a-f]{40}\b',  # SHA-1
    r'\b[0-9a-f]{64}\b',  # SHA-256
    # Additional dynamic patterns
    r'<meta name="generator" content="[^"]+">',
    r'<script nonce="[^"]+">',
    r'integrity="[^"]+"',
    r'data-nonce="[^"]+"',
]

# Common error patterns to detect
ERROR_PATTERNS = [
    r'(?:Exception|Error):\s*\w+',
    r'(?:SQL|Database) error',
    r'stack trace',
    r'syntax error',
    r'fatal error',
    r'500 internal',
    r'request (failed|timed out)',
]

# HTTPX SETTINGS
TIMEOUT = httpx.Timeout(connect=8.0, read=8.0, write=8.0, pool=30.0)
USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/134.0.0.0 YaBrowser/25.4.0.0 Safari/537.36"
]

# Setup logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('scan.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

init(autoreset=True)
print_lock = asyncio.Lock()
file_lock = asyncio.Lock()
sem_hosts = asyncio.Semaphore(MAX_CONCURRENT_URLS)


class AdaptiveThrottler:
    def __init__(self, initial_delay=0.1, max_delay=2.0, backoff_factor=1.5, recovery_factor=0.9, reset_interval=60):
        self.current_delay = initial_delay
        self.default_delay = initial_delay
        self.max_delay = max_delay
        self.backoff_factor = backoff_factor
        self.recovery_factor = recovery_factor
        self.success_count = 0
        self.failure_count = 0
        self.lock = asyncio.Lock()
        self.last_reset = time.time()
        self.reset_interval = reset_interval
        self.global_failures = 0  # Счетчик глобальных ошибок
        self.last_adjustment = time.time()  # Время последней корректировки
    
    async def success(self):
        async with self.lock:
            current_time = time.time()
            # Периодически сбрасываем задержку
            if current_time - self.last_reset > self.reset_interval:
                # Мягкий сброс в зависимости от общего числа ошибок
                if self.global_failures > 50:
                    # Много ошибок - сбрасываем до среднего значения
                    self.current_delay = min(self.default_delay * 1.5, self.max_delay * 0.5)
                elif self.global_failures > 20:
                    # Умеренное число ошибок - сбрасываем к начальному + небольшое увеличение
                    self.current_delay = min(self.default_delay * 1.2, self.max_delay * 0.3)
                else:
                    # Мало ошибок - полный сброс
                    self.current_delay = self.default_delay
                
                self.last_reset = current_time
                self.success_count = 0
                self.failure_count = 0
                self.global_failures = max(0, self.global_failures - 10)  # Уменьшаем счетчик глобальных ошибок
                return
            
            self.success_count += 1
            self.failure_count = 0
            
            # Не корректируем задержку слишком часто
            if current_time - self.last_adjustment < 5.0:  # Не корректируем чаще чем раз в 5 секунд
                return
                
            # Постепенно уменьшаем задержку при успешных запросах
            if self.success_count >= 5:  # Увеличиваем порог для большей стабильности
                self.current_delay = max(self.default_delay * 0.7, self.current_delay * self.recovery_factor)
                self.success_count = 0
                self.last_adjustment = current_time
    
    async def failure(self):
        async with self.lock:
            self.failure_count += 1
            self.global_failures += 1  # Увеличиваем глобальный счетчик
            self.success_count = 0
            
            current_time = time.time()
            # Не корректируем задержку слишком часто
            if current_time - self.last_adjustment < 2.0:  # Для ошибок более частая корректировка допустима
                return
                
            # Увеличиваем задержку при ошибках - более агрессивно при частых ошибках
            if self.global_failures > 30:
                # Много ошибок - значительное увеличение задержки
                self.current_delay = min(self.max_delay, self.current_delay * (self.backoff_factor * 1.5))
            else:
                # Умеренное число ошибок - стандартное увеличение
                self.current_delay = min(self.max_delay, self.current_delay * self.backoff_factor)
                
            self.last_adjustment = current_time
    
    async def delay(self):
        async with self.lock:
            return self.current_delay

# Создать экземпляр троттлера
throttler = AdaptiveThrottler()

class BatchManager:
    def __init__(self):
        self.steps = [INITIAL_BATCH, 50, 25, 10, 5, 1]
        self.idx = 0
        self.size = self.steps[self.idx]
        self.lock = asyncio.Lock()
    
    async def decrease(self):
        async with self.lock:
            if self.idx < len(self.steps) - 1:
                self.idx += 1
                self.size = self.steps[self.idx]
                return True
            return False
    
    async def reset_to_step(self, step_idx):
        async with self.lock:
            self.idx = min(step_idx, len(self.steps) - 1)
            self.size = self.steps[self.idx]
    
    async def get_size(self):
        async with self.lock:
            return self.size
    
    async def at_minimum(self):
        async with self.lock:
            return self.idx == len(self.steps) - 1

async def safe_print(text: str):
    async with print_lock:
        print(text)

async def safe_write(path: str, content: str):
    async with file_lock:
        async with aiofiles.open(path, 'a', encoding='utf-8') as f:
            await f.write(content)

def get_hash(body: bytes) -> str:
    return hashlib.sha256(body).hexdigest()

async def append_cb(url: str) -> str:
    rand = ''.join(random.choices(string.ascii_letters + string.digits, k=8))
    sep = '&' if '?' in url else '?'
    return f"{url}{sep}cb={rand}"

async def send_request(client: httpx.AsyncClient, url: str, headers: dict, retries=MAX_RETRIES):
    try:
        for attempt in range(retries):
            try:
                final_headers = {**headers, 'User-Agent': random.choice(USER_AGENTS)}
                
                # Используем таймаут для запроса
                # Заворачиваем в wait_for для гарантированного завершения
                resp = await asyncio.wait_for(
                    client.get(url, headers=final_headers, timeout=TIMEOUT, follow_redirects=False),
                    timeout=12.0  # Уменьшаем таймаут для ускорения всего процесса
                )
                
                content = resp.content
                await throttler.success()  # Отметить успешный запрос
                return resp.status_code, len(content), get_hash(content), resp.text, resp.headers
                
            except asyncio.CancelledError:
                # Быстро выходим при отмене задачи
                raise
                
            except (httpx.TimeoutException, asyncio.TimeoutError) as e:
                # Явно обрабатываем таймауты
                await throttler.failure()  # Отметить ошибку
                logger.debug(f"Timeout on attempt {attempt+1}: {url} - {str(e)}")
                
            except Exception as e:
                await throttler.failure()  # Отметить ошибку
                logger.debug(f"Request failed on attempt {attempt+1}: {url} - {str(e)}")
            
            # Проверка на отмену задачи перед повторной попыткой
            try:
                # Использовать адаптивную задержку
                delay = await throttler.delay()
                await asyncio.sleep(delay * (attempt + 1))
            except asyncio.CancelledError:
                # Быстро выходим при отмене задачи
                raise
                
    except asyncio.CancelledError:
        # Обрабатываем отмену задачи для корректного завершения
        logger.debug(f"Request to {url} was cancelled")
        raise
        
    except Exception as e:
        logger.error(f"Unhandled exception in send_request for {url}: {str(e)}")
    
    return None

async def normalize_content(content: str) -> str:
    """Remove dynamic content patterns before comparison."""
    # Create a copy of the content for normalization
    normalized = content
    
    # Apply all regex patterns
    for pattern in DYNAMIC_IGNORE_PATTERNS:
        normalized = re.sub(pattern, 'DYNAMIC_CONTENT_REMOVED', normalized)
    
    # Remove cache buster parameter from content if reflected
    normalized = re.sub(r'\bcb=[a-zA-Z0-9]{8}\b', 'CACHEBUSTER_REMOVED', normalized)
    
    # Remove common dynamic elements like unique IDs
    normalized = re.sub(r'\b[0-9a-f]{7,64}\b', 'HASH_REMOVED', normalized)
    
    # Try to detect and remove timestamp-like patterns
    normalized = re.sub(r'\b\d{10,13}\b', 'TIMESTAMP_REMOVED', normalized)
    
    # Remove whitespace variation
    normalized = re.sub(r'\s+', ' ', normalized)
    
    return normalized.strip()

def extract_dom_structure(html_content):
    """Extract the DOM structure for comparison, ignoring text content."""
    try:
        soup = BeautifulSoup(html_content, 'html.parser')
        
        # Remove all text nodes while preserving structure
        for element in soup.find_all(text=True):
            element.replace_with("")
            
        # Get all tag names in order of appearance
        structure = [tag.name for tag in soup.find_all()]
        return structure
    except Exception as e:
        logger.debug(f"Error extracting DOM structure: {str(e)}")
        return []

def detect_error_patterns(content):
    """Detect common error patterns in response."""
    error_matches = []
    for pattern in ERROR_PATTERNS:
        if re.search(pattern, content, re.IGNORECASE):
            error_matches.append(pattern)
    return error_matches

async def content_similarity(a: str, b: str) -> float:
    """Calculate content similarity with multiple metrics."""
    # Normalize content
    norm_a = await normalize_content(a)
    norm_b = await normalize_content(b)
    
    # Text similarity (fuzzy matching)
    text_similarity = fuzz.ratio(norm_a, norm_b) / 100
    
    # DOM structure similarity
    dom_a = extract_dom_structure(a)
    dom_b = extract_dom_structure(b)
    
    if dom_a and dom_b:
        # Use sequence matcher for structural comparison
        matcher = difflib.SequenceMatcher(None, dom_a, dom_b)
        dom_similarity = matcher.ratio()
    else:
        dom_similarity = text_similarity  # Fallback if DOM extraction fails
    
    # Error pattern detection
    error_a = detect_error_patterns(a)
    error_b = detect_error_patterns(b)
    
    # If one has errors and the other doesn't, they're definitely different
    if (error_a and not error_b) or (error_b and not error_a):
        return 0.0
    
    # Combined similarity score
    combined_similarity = (text_similarity + dom_similarity) / 2
    
    return combined_similarity

async def compare_responses(base_resp, test_resp):
    """
    Compare two responses using multiple metrics like Param Miner does.
    Returns similarity score and detailed analysis.
    """
    if not base_resp or not test_resp:
        return 0.0, ["Response unavailable"]
    
    base_status, base_len, base_hash, base_text, base_headers = base_resp
    test_status, test_len, test_hash, test_text, test_headers = test_resp
    
    details = []
    similarity_components = []
    
    # 1. Compare status codes
    status_similarity = 1.0 if base_status == test_status else 0.0
    similarity_components.append((status_similarity, STATUS_SIMILARITY_WEIGHT))
    
    if base_status != test_status:
        details.append(f"Status code changed: {base_status} → {test_status}")
    
    # 2. Compare content length
    length_diff = abs(base_len - test_len)
    length_similarity = max(0, 1 - (length_diff / max(base_len, 1)))
    similarity_components.append((length_similarity, LENGTH_SIMILARITY_WEIGHT))
    
    if length_diff > LENGTH_THRESHOLD:
        details.append(f"Content length changed: {base_len} → {test_len} (diff: {length_diff})")
    
    # 3. Compare content similarity (text and structure)
    content_sim = await content_similarity(base_text, test_text)
    similarity_components.append((content_sim, DOM_SIMILARITY_WEIGHT))
    
    if content_sim < STRUCTURAL_THRESHOLD:
        details.append(f"Content structure changed (similarity: {content_sim:.2f})")
    
    # 4. Check for reflections
    if COMMON_VALUE in test_text and COMMON_VALUE not in base_text:
        details.append("Value reflection detected")
        # Reflection is a strong signal
        similarity_components.append((0.0, 0.5))
    
    # 5. Check for error patterns
    base_errors = detect_error_patterns(base_text)
    test_errors = detect_error_patterns(test_text)
    
    if base_errors != test_errors:
        new_errors = set(test_errors) - set(base_errors)
        if new_errors:
            details.append(f"New error patterns: {', '.join(new_errors)}")
            similarity_components.append((0.0, 0.5))
    
    # 6. Header differences (redirects, content types)
    important_headers = ['location', 'content-type', 'content-disposition']
    for header in important_headers:
        base_val = base_headers.get(header)
        test_val = test_headers.get(header)
        
        if base_val != test_val:
            details.append(f"Header '{header}' changed: {base_val} → {test_val}")
            similarity_components.append((0.0, 0.2))
    
    # Calculate weighted average similarity
    if similarity_components:
        total_weight = sum(weight for _, weight in similarity_components)
        weighted_similarity = sum(sim * weight for sim, weight in similarity_components) / total_weight
    else:
        weighted_similarity = 1.0  # Default to identical if no components
    
    return weighted_similarity, details

async def calibrate(client: httpx.AsyncClient, url: str):
    """Calibrate baseline response by making multiple requests and finding the most consistent one."""
    results = []
    normalized_contents = []
    
    for _ in range(CALIBRATION_ATTEMPTS):
        test_url = await append_cb(url)
        r = await send_request(client, test_url, {})
        if not r:
            await asyncio.sleep(0.5)
            continue
            
        status, length, hash_val, text, headers = r
        normalized = await normalize_content(text)
        normalized_contents.append(normalized)
        results.append((status, length, hash_val, text, headers))
        await asyncio.sleep(0.3)
    
    if len(results) < 3:
        await safe_print(f"{Fore.YELLOW}[!] Not enough calibration data for {url}{Style.RESET_ALL}")
        return None
    
    # Build similarity matrix
    similarity_matrix = []
    for i in range(len(normalized_contents)):
        row = []
        for j in range(len(normalized_contents)):
            sim = fuzz.ratio(normalized_contents[i], normalized_contents[j]) / 100
            row.append(sim)
        similarity_matrix.append(row)
    
    # Find most consistent response (highest average similarity to others)
    avg_similarities = [sum(row) / len(row) for row in similarity_matrix]
    best_idx = avg_similarities.index(max(avg_similarities))
    
    # Log calibration quality
    avg_sim = avg_similarities[best_idx]
    if avg_sim >= 0.95:
        quality = f"{Fore.GREEN}Excellent"
    elif avg_sim >= 0.9:
        quality = f"{Fore.CYAN}Good"
    elif avg_sim >= 0.8:
        quality = f"{Fore.YELLOW}Fair"
    else:
        quality = f"{Fore.RED}Poor"
    
    await safe_print(f"{Fore.CYAN}[+] Calibrated {url} - {quality} quality ({avg_sim:.2f}){Style.RESET_ALL}")
    
    return results[best_idx]

async def verify_header_impact(client: httpx.AsyncClient, url: str, header: str, base_resp: tuple):
    """Verify if a header truly impacts the response by making multiple requests."""
    impacts = []
    reasons = []
    
    for _ in range(3):  # Try multiple times for consistency
        test_url = await append_cb(url)
        test_resp = await send_request(client, test_url, {header: COMMON_VALUE})
        if not test_resp:
            impacts.append(False)
            reasons.append("Request failed")
            continue
            
        # Advanced comparison using multiple metrics
        similarity, details = await compare_responses(base_resp, test_resp)
        
        # Consider it an impact if similarity is below threshold
        if similarity < SIMILARITY_THRESHOLD:
            impacts.append(True)
            reasons.append(", ".join(details[:2]) if details else "Response changed")
        else:
            impacts.append(False)
            reasons.append("No significant change")
    
    # Return True if the majority of tests show an impact
    is_impactful = sum(impacts) > len(impacts) / 2
    
    # Get the most common reason for the final result
    if is_impactful:
        impact_reasons = [r for i, r in zip(impacts, reasons) if i]
        reason = max(set(impact_reasons), key=impact_reasons.count) if impact_reasons else "Response changed"
    else:
        reason = "No consistent impact detected"
    
    return is_impactful, reason

async def binary_search_group(client, bm: BatchManager, url: str, base: tuple, names: list):
    """Search headers using binary search with batch processing."""
    found = []
    found_reasons = {}
    max_depth = 100  # Защита от бесконечного цикла
    current_depth = 0
    
    def stop_search():
        """Проверка превышения лимита в 10 заголовков."""
        return len(found) >= 10 or current_depth >= max_depth
    
    while names and not stop_search():
        current_depth += 1
        size = await bm.get_size()
        if size == 0:
            return found, found_reasons
            
        batch, names = names[:size], names[size:]
        
        # Устанавливаем таймаут для отдельных запросов
        try:
            async with asyncio.timeout(10):  # 10-секундный таймаут на запрос
                test_url = await append_cb(url)
                curr = await send_request(client, test_url, {h: COMMON_VALUE for h in batch})
        except asyncio.TimeoutError:
            curr = None
        
        if curr is None:
            decreased = await bm.decrease()
            if not decreased or await bm.at_minimum():
                # Individual testing when batch size is minimum
                for h in batch:
                    # Немедленный возврат если превышен лимит
                    if stop_search():
                        await safe_print(f"{Fore.CYAN}[!] Found 10 headers or reached max depth, stopping search for {url}{Style.RESET_ALL}")
                        return found[:10], dict(list(found_reasons.items())[:10])
                    
                    try:
                        async with asyncio.timeout(5):  # 5-секундный таймаут на одиночный запрос
                            test_url = await append_cb(url)
                            res = await send_request(client, test_url, {h: COMMON_VALUE})
                    except asyncio.TimeoutError:
                        res = None
                        
                    if res is None:
                        # Mark header as causing timeout - same as original implementation
                        if h not in found:
                            found.append(h)
                            found_reasons[h] = "Caused timeout"
                            await safe_print(f"{Fore.YELLOW}[!] Header {h} caused timeout{Style.RESET_ALL}")
                        continue
                        
                    # Compare response with baseline using advanced metrics
                    try:
                        async with asyncio.timeout(5):  # 5-секундный таймаут на проверку влияния
                            is_impactful, reason = await verify_header_impact(client, url, h, base)
                    except asyncio.TimeoutError:
                        # Предполагаем влияние при таймауте
                        is_impactful, reason = True, "Verification timed out"
                    
                    if is_impactful and h not in found:
                        found.append(h)
                        found_reasons[h] = reason
                        await safe_print(f"{Fore.GREEN}[+] Found impactful header: {h} - {reason}{Style.RESET_ALL}")
                
                await bm.reset_to_step(1)
                continue
            
            names = batch + names
            continue
        
        # Check for HTTP 431 status code
        status, _, _, _, _ = curr
        if status == 431:
            await safe_print(f"{Fore.YELLOW}[!] Got 431 status (Request Header Fields Too Large) for {url}, reducing batch size{Style.RESET_ALL}")
            decreased = await bm.decrease()
            if not decreased or await bm.at_minimum():
                await safe_print(f"{Fore.RED}[!] Already at minimum batch size, stopping search for {url}{Style.RESET_ALL}")
                return found, found_reasons
            names = batch + names
            continue
        
        # Compare batch response with baseline using advanced metrics
        try:
            async with asyncio.timeout(5):  # 5-секундный таймаут на сравнение
                similarity, details = await compare_responses(base, curr)
        except asyncio.TimeoutError:
            # Предполагаем отсутствие сходства при таймауте
            similarity, details = 0, ["Comparison timed out"]
        
        # If similarity is below threshold, this batch contains impactful headers
        if similarity < SIMILARITY_THRESHOLD:
            if len(batch) == 1:
                # Немедленный возврат если превышен лимит
                if stop_search():
                    await safe_print(f"{Fore.CYAN}[!] Found 10 headers or reached max depth, stopping search for {url}{Style.RESET_ALL}")
                    return found[:10], dict(list(found_reasons.items())[:10])
                
                # Verify single header impact
                h = batch[0]
                try:
                    async with asyncio.timeout(5):  # 5-секундный таймаут на проверку влияния
                        is_impactful, reason = await verify_header_impact(client, url, h, base)
                except asyncio.TimeoutError:
                    # Предполагаем влияние при таймауте
                    is_impactful, reason = True, "Verification timed out"
                
                if is_impactful and h not in found:
                    found.append(h)
                    found_reasons[h] = reason
                    await safe_print(f"{Fore.GREEN}[+] Found impactful header: {h} - {reason}{Style.RESET_ALL}")
            else:
                # Split batch and continue binary search
                mid = len(batch) // 2
                
                # Проверка левой половины
                l_found, l_reasons = await binary_search_group(client, bm, url, base, batch[:mid])
                
                # Добавляем только уникальные заголовки
                for h in l_found:
                    if h not in found:
                        found.append(h)
                        found_reasons[h] = l_reasons.get(h, "")
                
                # Немедленный возврат если превышен лимит
                if stop_search():
                    await safe_print(f"{Fore.CYAN}[!] Found 10 headers or reached max depth, stopping search for {url}{Style.RESET_ALL}")
                    return found[:10], dict(list(found_reasons.items())[:10])
                
                # Проверка правой половины
                r_found, r_reasons = await binary_search_group(client, bm, url, base, batch[mid:])
                
                # Добавляем только уникальные заголовки
                for h in r_found:
                    if h not in found:
                        found.append(h)
                        found_reasons[h] = r_reasons.get(h, "")
                
                # Финальная проверка
                if stop_search():
                    await safe_print(f"{Fore.CYAN}[!] Found 10 headers or reached max depth, stopping search for {url}{Style.RESET_ALL}")
                    return found[:10], dict(list(found_reasons.items())[:10])
    
    return found[:10], dict(list(found_reasons.items())[:10])

# New function to test for cache poisoning with a discovered header
async def test_cache_poisoning(client, url, header, base_resp):
    """
    Test if a header can be used for cache poisoning attacks using ParamMiner's technique.
    Returns a list of successful poisonings with details.
    """
    # Generate a unique test identifier for logging
    test_id = f"cache_test_{int(time.time())}_{url.replace('://', '_').replace('/', '_')}_{header}"
    
    # Function for detailed request and response logging
    async def log_request_response(step, req_url, req_headers, resp_data, path):
        if not resp_data:
            log_entry = {
                "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                "test_id": test_id,
                "header_tested": header,
                "url": url,
                "path": path,
                "step": step,
                "request_url": req_url,
                "request_headers": req_headers,
                "response": "REQUEST FAILED"
            }
        else:
            status, length, hash_val, text, resp_headers = resp_data
            headers_dict = dict(resp_headers.items())
            
            # Limit response body size for logs
            if len(text) > 2000:
                text = text[:2000] + "... [TRUNCATED]"
            
            log_entry = {
                "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                "test_id": test_id,
                "header_tested": header,
                "url": url,
                "path": path,
                "step": step,
                "request_url": req_url,
                "request_headers": req_headers,
                "response": {
                    "status": status,
                    "length": length,
                    "hash": hash_val,
                    "headers": headers_dict,
                    "body": text
                }
            }
        
        # Write to log in readable JSON format
        log_message = json.dumps(log_entry, indent=2, ensure_ascii=False)
        async with aiofiles.open('debug.log', 'a', encoding='utf-8') as f:
            await f.write(f"\n--- CACHE POISONING TEST LOG ENTRY ---\n")
            await f.write(log_message)
            await f.write("\n--- END OF LOG ENTRY ---\n\n")
    
    # Test paths - check various common paths for poisoning
    test_paths = [
        "/",                    # Root path
        "/robots.txt",          # Common static file
        "/static/h3ll.js",         # Another common static file
        "/sitemap.xml",         # Common XML file
        "/assets/main.css"      # Common asset file
    ]
    
    poisoning_results = []
    
    for path in test_paths:
        # Build full URL for the path
        if path != "/" and not url.endswith("/"):
            full_url = f"{url}{path}"
        else:
            full_url = f"{url}{path[1:]}" if path.startswith("/") and url.endswith("/") else f"{url}{path}"
        
        # Generate unique cache keys for each step
        baseline_key = ''.join(random.choices(string.ascii_letters + string.digits, k=8))
        poison_key = ''.join(random.choices(string.ascii_letters + string.digits, k=8))
        verify_key = poison_key  # Use same key for verification (important!)
        control_key = ''.join(random.choices(string.ascii_letters + string.digits, k=8))
        
        # ===== STEP 1: Baseline request (without header) =====
        base_url = f"{full_url}{'&' if '?' in full_url else '?'}cb={baseline_key}"
        baseline = await send_request(client, base_url, {})
        await log_request_response("1-BASELINE", base_url, {}, baseline, path)
        
        if not baseline:
            logger.debug(f"Skipping cache poisoning test for {path} - baseline request failed")
            continue
        
        # ===== STEP 2: Poisoning request (with header) =====
        # Use a different cache key than baseline
        poison_url = f"{full_url}{'&' if '?' in full_url else '?'}cb={poison_key}"
        poisoning_headers = {header: COMMON_VALUE}
        
        # Send multiple poisoning requests to ensure caching
        poison_resp = None
        for i in range(3):
            poison_resp = await send_request(client, poison_url, poisoning_headers)
            await log_request_response(f"2-POISON_{i+1}", poison_url, poisoning_headers, poison_resp, path)
            if not poison_resp:
                break
            await asyncio.sleep(0.3)  # Small delay between requests
        
        if not poison_resp:
            logger.debug(f"Skipping cache poisoning test for {path} - poisoning requests failed")
            continue
        
        # ===== STEP 3: Verification request (same URL as poisoning but WITHOUT header) =====
        # CRITICAL: This must use the same cache key as the poisoning request
        verify_url = poison_url  # Same URL with same cache key as poisoning
        verify_resp = await send_request(client, verify_url, {})
        await log_request_response("3-VERIFY", verify_url, {}, verify_resp, path)
        
        if not verify_resp:
            logger.debug(f"Skipping cache poisoning test for {path} - verification request failed")
            continue
        
        # ===== STEP 4: Control request (different URL without header) =====
        # Use a different cache key to confirm unique caching behavior
        control_url = f"{full_url}{'&' if '?' in full_url else '?'}cb={control_key}"
        control_resp = await send_request(client, control_url, {})
        await log_request_response("4-CONTROL", control_url, {}, control_resp, path)
        
        if not control_resp:
            logger.debug(f"Skipping control check for {path} - control request failed")
            continue
        
        # ===== Analysis of results =====
        base_status, base_length, base_hash, base_text, base_headers = baseline
        poison_status, poison_length, poison_hash, poison_text, poison_headers = poison_resp
        verify_status, verify_length, verify_hash, verify_text, verify_headers = verify_resp
        control_status, control_length, control_hash, control_text, control_headers = control_resp
        
        # Key poisoning indicators:
        # 1. Verify response should be more similar to poison response than to baseline/control
        # 2. Verify should contain the injected value but baseline/control shouldn't
        # 3. Verify + Poison hash should match but differ from Baseline + Control
        
        # Compare verify with poison (should be similar for poisoning)
        verify_to_poison_sim = await content_similarity(verify_text, poison_text)
        
        # Compare verify with baseline (should be different for poisoning)
        verify_to_base_sim = await content_similarity(verify_text, base_text)
        
        # Compare verify with control (should be different for poisoning)
        verify_to_control_sim = await content_similarity(verify_text, control_text)
        
        # Check for test value reflection
        base_reflects = COMMON_VALUE in base_text
        verify_reflects = COMMON_VALUE in verify_text
        control_reflects = COMMON_VALUE in control_text
        
        # Main decision logic for detecting cache poisoning
        is_poisoned = False
        reason = ""
        
        # Primary condition: verify must be more similar to poison than to both baseline and control
        primary_condition = (verify_to_poison_sim > 0.9 and 
                             verify_to_poison_sim > verify_to_base_sim + 0.1 and
                             verify_to_poison_sim > verify_to_control_sim + 0.1)
        
        # Secondary condition: test value reflection in verify but not in baseline/control
        secondary_condition = (verify_reflects and not base_reflects and not control_reflects)
        
        # Hash comparison (strongest evidence)
        hash_match = verify_hash == poison_hash and verify_hash != base_hash and verify_hash != control_hash
        
        # Combined decision
        if hash_match:
            is_poisoned = True
            reason = "Strong evidence: Response hashes match between poisoned and verification requests"
        elif primary_condition:
            is_poisoned = True
            reason = f"Response similarity: Verification matches poisoned ({verify_to_poison_sim:.2f}) but differs from baseline ({verify_to_base_sim:.2f})"
        elif secondary_condition:
            is_poisoned = True
            reason = f"Test value '{COMMON_VALUE}' reflected in verification response but not in baseline/control"
        
        # Log the detailed analysis
        analysis_log = {
            "timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "test_id": test_id,
            "header_tested": header,
            "url": url,
            "path": path,
            "is_poisoned": is_poisoned,
            "reason": reason,
            "details": {
                "hash_match": hash_match,
                "verify_poison_similarity": verify_to_poison_sim,
                "verify_base_similarity": verify_to_base_sim,
                "verify_control_similarity": verify_to_control_sim,
                "base_reflects": base_reflects,
                "verify_reflects": verify_reflects,
                "control_reflects": control_reflects,
                "base_hash": base_hash,
                "poison_hash": poison_hash,
                "verify_hash": verify_hash,
                "control_hash": control_hash
            }
        }
        
        async with aiofiles.open('debug.log', 'a', encoding='utf-8') as f:
            await f.write(f"\n--- CACHE POISONING ANALYSIS ---\n")
            await f.write(json.dumps(analysis_log, indent=2, ensure_ascii=False))
            await f.write("\n--- END OF ANALYSIS ---\n\n")
        
        if is_poisoned:
            poisoning_results.append((path, is_poisoned, reason, verify_status, verify_length))
    
    return poisoning_results


# Modify the process_url function to include cache poisoning tests
async def process_url(url: str):
    """Process a single URL to find impactful headers."""
    await safe_print(f"\n{Fore.MAGENTA}[~] Processing host: {url}{Style.RESET_ALL}")
    start_time = time.time()
    
    # Parse URL to get domain for reporting
    try:
        parsed_url = urlparse(url)
        domain = parsed_url.netloc or url
    except ValueError as e:
        await safe_print(f"{Fore.RED}[!] Invalid URL format for {url}: {str(e)}{Style.RESET_ALL}")
        await safe_write(RESULT_FILE, f"[!] Skipped invalid URL: {url} - Error: {str(e)}\n" + "="*50 + "\n")
        return
    
    # Создаем клиента вне блока try-except для гарантированного закрытия
    limits = httpx.Limits(
        max_connections=50,
        max_keepalive_connections=30,
        keepalive_expiry=15.0
    )
    
    client = httpx.AsyncClient(http2=True, verify=False, limits=limits)
    
    # Список всех созданных задач, которые нужно отменить при ошибке
    active_tasks = []
    
    try:
        async with sem_hosts:
            # Используем глобальный таймаут с корректной очисткой
            try:
                # Увеличиваем общий таймаут для уменьшения вероятности зависания
                async with asyncio.timeout(180):  # Уменьшаем с 400 до 180 секунд
                    # Step 1: Calibrate baseline response
                    base = None
                    try:
                        async with asyncio.timeout(30):  # Уменьшаем с 60 до 30 секунд
                            base = await calibrate(client, url)
                    except asyncio.TimeoutError:
                        await safe_print(f"{Fore.RED}[!] Calibration timed out for {url}{Style.RESET_ALL}")
                        return
                        
                    if not base:
                        await safe_print(f"{Fore.RED}[!] Calibration failed for {url}{Style.RESET_ALL}")
                        return
                        
                    bs, bl, bh, _, base_headers = base
                    content_type = base_headers.get('content-type', 'unknown')
                    await safe_print(f"{Fore.CYAN}[~] Baseline: [{bs}] CL:{bl} Type:{content_type}{Style.RESET_ALL}")
                    
                    # Step 2: Search for impactful headers
                    found = []
                    reasons = {}
                    try:
                        async with asyncio.timeout(60):  # Уменьшаем с 120 до 60 секунд
                            bm = BatchManager()
                            names = ALL_HEADER_NAMES.copy()
                            found, reasons = await binary_search_group(client, bm, url, base, names)
                    except asyncio.TimeoutError:
                        await safe_print(f"{Fore.RED}[!] Header search timed out for {url}{Style.RESET_ALL}")
                        found = []
                        reasons = {}
    
                    # Check if we found too many headers (10+)
                    if len(found) >= 10:
                        await safe_print(f"{Fore.CYAN}[!] Stopping {url} - found {len(found)} headers{Style.RESET_ALL}")
                        lines = [f"[!] Host {domain} skipped - found {len(found)} impactful headers"]
                        block = "\n".join(lines) + "\n" + "="*50 + "\n"
                        await safe_print(block)
                        await safe_write(RESULT_FILE, block)
                        return  # Stop processing this host
                    
                    # Step 3: Verification and cache poisoning tests
                    lines = []
                    verification_tasks = []
                    poisoning_tasks = []
                    
                    # Prepare tasks for verified headers (excluding timeout headers)
                    filtered_headers = [hdr for hdr in found if "timeout" not in reasons.get(hdr, "").lower()]
                    
                    # Ограничиваем количество тестов для уменьшения нагрузки
                    cache_test_headers = filtered_headers[:1] if len(filtered_headers) > 1 else filtered_headers
                    
                    for hdr in filtered_headers:
                        task = asyncio.create_task(verify_single_header_with_sem(verification_sem, client, url, hdr, base))
                        verification_tasks.append(task)
                        active_tasks.append(task)
                    
                    for hdr in cache_test_headers:
                        task = asyncio.create_task(test_cache_poisoning_with_sem(poisoning_sem, client, url, hdr, base))
                        poisoning_tasks.append(task)
                        active_tasks.append(task)
                    
                    # Execute tasks with proper cancellation
                    verification_results = []
                    poisoning_results = []
                    
                    try:
                        async with asyncio.timeout(40):  # Уменьшаем с 120 до 40 секунд
                            if verification_tasks:
                                verification_results = await asyncio.gather(*verification_tasks)
                    except asyncio.TimeoutError:
                        await safe_print(f"{Fore.RED}[!] Verification tests timed out for {url}{Style.RESET_ALL}")
                        # Отменяем все зависшие задачи
                        for task in verification_tasks:
                            if not task.done():
                                task.cancel()
                        
                    try:
                        async with asyncio.timeout(60):  # Уменьшаем с 180 до 60 секунд
                            if poisoning_tasks:
                                poisoning_results = await asyncio.gather(*poisoning_tasks)
                    except asyncio.TimeoutError:
                        await safe_print(f"{Fore.RED}[!] Poisoning tests timed out for {url}{Style.RESET_ALL}")
                        # Отменяем все зависшие задачи
                        for task in poisoning_tasks:
                            if not task.done():
                                task.cancel()
                    
                    # Process verification and poisoning results
                    cache_poisoning_results = {}
                    
                    if found:
                        lines.append(f"[+] Results for {domain} ({url}):")
                        
                        # Process verification results
                        for hdr, verification in zip(filtered_headers[:len(verification_results)], verification_results):
                            status, length, content_type, details = verification
                            lines.append(f"  {hdr} => [{status}] CL:{length} Type:{content_type}")
                            if details:
                                lines.append(f"    Details: {details}")
                        
                        # Process cache poisoning results
                        if poisoning_results:
                            lines.append(f"\n[~] Cache Poisoning Tests:")
                            
                            for (hdr, poisoning) in zip(cache_test_headers[:len(poisoning_results)], poisoning_results):
                                if poisoning:
                                    # Found cache poisoning vulnerability!
                                    await safe_print(f"{Fore.RED}[!] CACHE POISONING detected with header: {hdr}{Style.RESET_ALL}")
                                    lines.append(f"  [!] CACHE POISONING with header: {hdr}")
                                    
                                    for path, is_poisoned, reason, status, length in poisoning:
                                        if is_poisoned:
                                            lines.append(f"    - Path: {path} - [{status}] CL:{length}")
                                            lines.append(f"      {reason}")
                                    
                                    # Store for later analysis
                                    cache_poisoning_results[hdr] = poisoning
                                else:
                                    lines.append(f"  [-] No cache poisoning with header: {hdr}")
                    else:
                        lines.append(f"[+] No impactful headers found for {domain} ({url})")
                    
                    # Calculate and report scan time
                    elapsed = time.time() - start_time
                    lines.append(f"[i] Scan completed in {elapsed:.2f} seconds")
                    
                    # Add a summary of cache poisoning findings
                    if cache_poisoning_results:
                        vulnerable_paths = set()
                        for hdr, results in cache_poisoning_results.items():
                            for path, is_poisoned, _, _, _ in results:
                                if is_poisoned:
                                    vulnerable_paths.add(path)
                        
                        if vulnerable_paths:
                            lines.append(f"\n[!!!] CACHE POISONING VULNERABILITY SUMMARY:")
                            lines.append(f"  Host: {domain}")
                            lines.append(f"  Vulnerable paths: {', '.join(vulnerable_paths)}")
                            lines.append(f"  Exploitable headers: {', '.join(cache_poisoning_results.keys())}")
                            lines.append(f"  Recommendation: This server appears vulnerable to cache poisoning attacks.")
                    
                    block = "\n".join(lines) + "\n" + "="*50 + "\n"
                    await safe_print(block)
                    await safe_write(RESULT_FILE, block)
                    
            except asyncio.TimeoutError:
                await safe_print(f"{Fore.RED}[!] Complete processing timed out for {url}{Style.RESET_ALL}")
                await safe_write(RESULT_FILE, f"[!] Processing timed out for {url} after {time.time() - start_time:.2f}s\n" + "="*50 + "\n")
                
    except Exception as e:
        await safe_print(f"{Fore.RED}[!] Error processing {url}: {str(e)}{Style.RESET_ALL}")
        await safe_write(RESULT_FILE, f"[!] Error processing {url}: {str(e)}\n" + "="*50 + "\n")
        
    finally:
        # Отменяем все активные задачи
        for task in active_tasks:
            if not task.done():
                task.cancel()
        
        # Собираем мусор
        import gc
        gc.collect()
        
        # Гарантированно закрываем клиент
        try:
            await client.aclose()
        except Exception as e:
            await safe_print(f"{Fore.RED}[!] Error closing client for {url}: {str(e)}{Style.RESET_ALL}")

# Обёртки с семафорами для верификации и тестов
async def verify_single_header_with_sem(sem, client, url, hdr, base):
    async with sem:
        return await verify_single_header(client, url, hdr, base)

async def test_cache_poisoning_with_sem(sem, client, url, hdr, base):
    async with sem:
        return await test_cache_poisoning(client, url, hdr, base)

async def verify_single_header(client, url, hdr, base):
    """Verify a single header's impact with detailed reporting."""
    # Make multiple requests with the header and analyze results
    results = []
    
    for _ in range(2):  # 2 verification attempts
        test_url = await append_cb(url)
        res = await send_request(client, test_url, {hdr: COMMON_VALUE})
        
        if not res:
            continue
            
        results.append(res)
    
    if not results:
        # Failed to get verification response
        return "TIMEOUT", "N/A", "N/A", "Timeout during verification"
    
    # Use the most consistent result
    res = results[0]  # Default to first if only one
    
    if len(results) > 1:
        # Compare the results for consistency
        status1, length1, hash1, _, _ = results[0]
        status2, length2, hash2, _, _ = results[1]
        
        # If results are inconsistent, note this as it might be relevant
        if status1 != status2 or abs(length1 - length2) > LENGTH_THRESHOLD:
            inconsistent = True
        else:
            inconsistent = False
    else:
        inconsistent = False
    
    status, length, _, text, headers = res
    base_status, base_len, _, base_text, base_headers = base
    
    # Get content type for reporting
    content_type = headers.get('content-type', 'unknown')
    
    # Compare with baseline to extract differences
    similarity, details = await compare_responses(base, res)
    
    # Check for reflections
    reflection_check = COMMON_VALUE in text and COMMON_VALUE not in base_text
    
    # Build detailed analysis
    analysis = []
    
    if inconsistent:
        analysis.append("Inconsistent responses detected")
    
    if details:
        analysis.extend(details[:3])  # Top 3 differences
    
    if reflection_check:
        analysis.append("Value reflection confirmed")
    
    # Check for redirection changes
    base_loc = base_headers.get('location')
    test_loc = headers.get('location')
    
    if base_loc != test_loc and test_loc:
        analysis.append(f"Redirect to: {test_loc}")
    
    # Format the result
    detail_str = "; ".join(analysis) if analysis else "Response changed"
    return status, length, content_type.split(';')[0], detail_str

async def validate_urls(urls):
    """Validate URLs and filter out invalid ones."""
    valid_urls = []
    for url in urls:
        try:
            # Basic validation of URL format
            parsed = urlparse(url)
            if parsed.scheme and parsed.netloc:
                valid_urls.append(url)
            else:
                await safe_print(f"{Fore.YELLOW}[!] Skipping invalid URL format: {url}{Style.RESET_ALL}")
        except ValueError as e:
            await safe_print(f"{Fore.YELLOW}[!] Skipping invalid URL: {url} - {str(e)}{Style.RESET_ALL}")
    
    return valid_urls

async def main():
    global ALL_HEADER_NAMES
    global verification_sem, poisoning_sem
    
    # Создаем глобальные семафоры для всего приложения
    verification_sem = asyncio.Semaphore(5)  # Уменьшаем лимит для стабильности
    poisoning_sem = asyncio.Semaphore(3)     # Уменьшаем лимит для стабильности
    
    # Инициализация debug лог-файла
    with open('debug.log', 'w', encoding='utf-8') as f:
        f.write(f"=== CACHE POISONING DEBUG LOG - STARTED AT {datetime.now().strftime('%Y-%m-%d %H:%M:%S')} ===\n\n")
    
    # Load headers and URLs
    try:
        ALL_HEADER_NAMES = [l.strip() for l in open(HEADERS_FILE) if l.strip()]
        raw_urls = [l.strip() for l in open(URLS_FILE) if l.strip()]
    except FileNotFoundError as e:
        await safe_print(f"{Fore.RED}[!] Error: {str(e)}{Style.RESET_ALL}")
        return
    
    if not ALL_HEADER_NAMES:
        await safe_print(f"{Fore.RED}[!] Error: No headers found in {HEADERS_FILE}{Style.RESET_ALL}")
        return
        
    if not raw_urls:
        await safe_print(f"{Fore.RED}[!] Error: No URLs found in {URLS_FILE}{Style.RESET_ALL}")
        return
    
    # Validate URLs before processing
    urls = await validate_urls(raw_urls)
    
    if not urls:
        await safe_print(f"{Fore.RED}[!] Error: No valid URLs to scan{Style.RESET_ALL}")
        return
    
    # Initialize result file
    open(RESULT_FILE, 'w').close()
    
    # Print scan info
    await safe_print(f"{Fore.GREEN}[+] Starting Param Miner style header scan{Style.RESET_ALL}")
    await safe_print(f"{Fore.GREEN}[+] Loaded {len(ALL_HEADER_NAMES)} headers and {len(urls)} URLs (filtered from {len(raw_urls)}){Style.RESET_ALL}")
    await safe_print(f"{Fore.GREEN}[+] Using enhanced content similarity analysis{Style.RESET_ALL}")
    await safe_print(f"{Fore.GREEN}[+] Similarity threshold: {SIMILARITY_THRESHOLD}{Style.RESET_ALL}")
    
    # Process URLs with improved task management
    start_time = time.time()
    
    # Уменьшаем размер пакета для лучшей обработки ошибок
    batch_size = 15  # Уменьшено с 30 до 15
    
    # Список всех активных задач для правильной очистки
    all_tasks = []
    
    for i in range(0, len(urls), batch_size):
        batch = urls[i:i+batch_size]
        await safe_print(f"{Fore.CYAN}[+] Processing batch {i//batch_size + 1}/{(len(urls)+batch_size-1)//batch_size} ({len(batch)} URLs){Style.RESET_ALL}")
        
        # Устанавливаем таймаут для всей пакетной обработки
        try:
            # Создаем задачи
            tasks = []
            for u in batch:
                task = asyncio.create_task(process_url(u))
                tasks.append(task)
                all_tasks.append(task)
            
            # Выполняем с ограничением по времени и правильной обработкой исключений
            async with asyncio.timeout(450):  # 7.5 минут на пакет
                for i, task in enumerate(asyncio.as_completed(tasks)):
                    try:
                        await task
                    except asyncio.CancelledError:
                        await safe_print(f"{Fore.YELLOW}[!] Task {i+1} was cancelled{Style.RESET_ALL}")
                    except Exception as e:
                        await safe_print(f"{Fore.RED}[!] Task {i+1} failed with: {str(e)}{Style.RESET_ALL}")
                
        except asyncio.TimeoutError:
            await safe_print(f"{Fore.RED}[!] Batch processing timed out, moving to next batch{Style.RESET_ALL}")
            # Отменяем все незавершенные задачи в текущем пакете
            for task in tasks:
                if not task.done():
                    task.cancel()
        except Exception as e:
            await safe_print(f"{Fore.RED}[!] Batch processing failed with: {str(e)}{Style.RESET_ALL}")
        
        # Пауза между пакетами для освобождения ресурсов и точка синхронизации
        await asyncio.sleep(15)  # Увеличиваем паузу для лучшего освобождения ресурсов
        
        # Завершаем все активные задачи прежде чем двигаться дальше
        pending_tasks = [t for t in tasks if not t.done()]
        if pending_tasks:
            await safe_print(f"{Fore.YELLOW}[!] Waiting for {len(pending_tasks)} pending tasks to complete or cancel{Style.RESET_ALL}")
            # Предоставляем дополнительное время для завершения
            for _ in range(5):  # 5 попыток 
                if not any(not t.done() for t in tasks):
                    break
                await asyncio.sleep(1)
            
            # Принудительно отменяем все оставшиеся
            for task in tasks:
                if not task.done():
                    task.cancel()
        
        # Принудительно собираем мусор для освобождения ресурсов
        import gc
        gc.collect()
    
    # Финальная очистка - убеждаемся, что все задачи завершены
    await safe_print(f"{Fore.CYAN}[+] Finalizing and cleaning up...{Style.RESET_ALL}")
    pending_tasks = [t for t in all_tasks if not t.done()]
    if pending_tasks:
        await safe_print(f"{Fore.YELLOW}[!] Cancelling {len(pending_tasks)} remaining tasks{Style.RESET_ALL}")
        for task in pending_tasks:
            task.cancel()
    
    # Report completion
    elapsed = time.time() - start_time
    completion_message = f"\n{Fore.GREEN}Scan completed in {elapsed:.2f} seconds.{Style.RESET_ALL}"
    await safe_print(completion_message)
    await safe_write(RESULT_FILE, f"Scan completed in {elapsed:.2f} seconds.\n")

if __name__ == '__main__':
    asyncio.run(main())