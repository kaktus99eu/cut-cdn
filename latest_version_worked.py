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

# logging.getLogger("httpx").setLevel(logging.DEBUG)
# logging.getLogger("httpcore").setLevel(logging.DEBUG)


# Глобальные константы для списков слов
# (Можно вынести их за пределы функции, чтобы они определялись один раз)

TOKEN_PREFIXES = sorted(list(set([
    "id", "uid", "app", "api", "user", "auth", "session", "admin", "test", "debug",
    "dev", "internal", "proxy", "client", "server",
    "true", "real", "original", "source", "target", "dest",
    "custom", "config", "service", "data", "cache",
    "request", "response", "header", # "query", "body" - менее релевантны как префиксы для имен *заголовков*
    "rest", "ws", "web", "cdn", "geo", "core"
])))

TOKEN_SUFFIXES = sorted(list(set([
    "id", "uid", "uuid", "key", "token", "secret", "auth", "pass",
    "user", "username", "name", "login", "account", "profile", "info",
    "admin", "role", "group", "access", "privilege",
    "debug", "test", "trace", "log", "level", "stats",
    "enabled", "disabled", "active", "status", "state", "mode", "flag", "switch", "toggle",
    "override", "force", "bypass", "check", "validate",
    "version", "env", "config", "setting", "options",
    "type", "format",
    "value", "data", "content", "text",
    "url", "uri", "path", "host", "port",
    "payload", "input", "output",
    "query", "filter", "search",
    "lang", "locale", "ip",
    "callback", "cb", "redirect", "next", "origin", "referer",
    "date", "time", "timestamp", "ts", "nonce", "hash", "signature",
    "api", "service", "sessionid", "csrf",
    "action", "method", "control"
])))

# Основные префиксы для HTTP заголовков, которые мы будем добавлять в конце
HTTP_HEADER_PREFIXES_WRAPPERS = ["X", "Sec", "App", "Internal"] # Используем полные слова для ясности


# ========== CONFIG ==========
URLS_FILE = 'urls.txt'
HEADERS_FILE = 'headers.txt'
RESULT_FILE = 'results.txt'
LENGTH_THRESHOLD = 50
COMMON_VALUE = "h3ll0w0rld"
INITIAL_BATCH = 100
MAX_RETRIES = 1
MAX_CONCURRENT_URLS = 50  # Parallel hosts
MAX_CONCURRENT_BATCHES = 50  # Parallel batch searches per host
# Calibration settings
CALIBRATION_ATTEMPTS = 5
SIMILARITY_THRESHOLD = 0.92  # Lowered to be more sensitive
# Enhanced analysis settings
DOM_SIMILARITY_WEIGHT = 0.5
LENGTH_SIMILARITY_WEIGHT = 0.2
STATUS_SIMILARITY_WEIGHT = 0.3
STRUCTURAL_THRESHOLD = 0.85  # Threshold for structural similarity
MAX_RESPONSE_SIZE_BYTES = 1 * 1024 * 1024 # 1 MB

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

logging.basicConfig(
    level=logging.WARNING,               # или нужный вам уровень
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler()         # только вывод в консоль
    ]
)
logger = logging.getLogger(__name__)

# HTTPX SETTINGS
TIMEOUT = httpx.Timeout(connect=8.0, read=8.0, write=8.0, pool=30.0)
USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/134.0.0.0 YaBrowser/25.4.0.0 Safari/537.36"
]

# import logging
# logging.basicConfig(
#     level=logging.INFO,
#     format='%(asctime)s - %(levelname)s - %(message)s',
#     handlers=[
#         logging.FileHandler('scan.log'),   # ← УДАЛЯЕМ ЭТУ СТРОКУ
#         logging.StreamHandler()
#     ]
# )
# logger = logging.getLogger(__name__)

init(autoreset=True)
print_lock = asyncio.Lock()
file_lock = asyncio.Lock()
sem_hosts = asyncio.Semaphore(MAX_CONCURRENT_URLS)


class AdaptiveThrottler:
    def __init__(self, initial_delay=0.05, max_delay=0.1, backoff_factor=1.1, recovery_factor=0.95, reset_interval=60000): # Изменены значения по умолчанию для теста
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
        self.global_failures = 0
        self.last_adjustment = time.time()
    
    async def success(self):
        async with self.lock:
            self.success_count += 1 # Счетчик оставим
            self.failure_count = 0   # Счетчик оставим
            # current_time = time.time()
            # if current_time - self.last_reset > self.reset_interval:
            #     # ... (логика сброса self.current_delay) ...
            #     # ЗАКОММЕНТИРУЕМ ИЗМЕНЕНИЕ self.current_delay
            #     return
            
            # if current_time - self.last_adjustment < 5.0:
            #     return
                
            # if self.success_count >= 5:
            #     # ЗАКОММЕНТИРУЕМ ИЗМЕНЕНИЕ self.current_delay
            #     # self.current_delay = max(self.default_delay * 0.7, self.current_delay * self.recovery_factor)
            #     self.success_count = 0
            #     self.last_adjustment = current_time
            pass # Ничего не делаем с задержкой

    async def failure(self):
        async with self.lock:
            self.failure_count += 1 # Счетчик оставим
            self.global_failures += 1 # Счетчик оставим
            self.success_count = 0    # Счетчик оставим
            
            # current_time = time.time()
            # if current_time - self.last_adjustment < 2.0:
            #     return
                
            # if self.global_failures > 30:
            #     # ЗАКОММЕНТИРУЕМ ИЗМЕНЕНИЕ self.current_delay
            #     # self.current_delay = min(self.max_delay, self.current_delay * (self.backoff_factor * 1.5))
            #     pass
            # else:
            #     # ЗАКОММЕНТИРУЕМ ИЗМЕНЕНИЕ self.current_delay
            #     # self.current_delay = min(self.max_delay, self.current_delay * self.backoff_factor)
            #     pass
            # self.last_adjustment = current_time
            pass # Ничего не делаем с задержкой
    
    async def delay(self):
        async with self.lock:
            # Возвращаем небольшую фиксированную задержку для теста
            return 0.05 # Например, 50 миллисекунд. Подберите значение.
            # Или self.default_delay, если хотите использовать initial_delay из конструктора
            # return self.default_delay

# Создать экземпляр троттлера
throttler = AdaptiveThrottler()
async def log_time_taken(operation_name: str, start_time: float, url_context: str = "", detail: str = ""):
    elapsed = time.monotonic() - start_time
    # Логируем, если операция заняла заметное время, например, больше 0.05 секунды (50 мс)
    # или если это специфический лог, который мы всегда хотим видеть (помечен ALWAYS_LOG).
    if elapsed > 0.05 or "ALWAYS_LOG" in operation_name: 
        log_message = f"{Fore.MAGENTA}[TIMER]{Style.RESET_ALL} {operation_name}"
        if detail:
            log_message += f" ({detail})"
        if url_context:
            log_message += f" for {url_context}"
        log_message += f" took {elapsed:.3f}s"
        
        # Используем logger.warning, чтобы сообщения точно выводились при текущих настройках
        # В production можно переключить на logger.debug или убрать/изменить условие if
        logger.warning(log_message)

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

def generate_hostname_based_core_names(hostname: str) -> set:
    core_names = set()
    
    # 1. Токенизация хоста
    # "checks.edadeal.yandex.ru" -> ["checks", "edadeal", "yandex", "ru"]
    # Исключаем слишком короткие или общие (как "ru", "com", "org", "net", "www")
    # и также слишком длинные отдельные части, если они не несут смысла как токен
    host_tokens = [
        part.lower() for part in hostname.split('.') 
        if len(part) > 2 and len(part) < 20 and part not in ["com", "org", "net", "io", "dev", "app", "www", "corp", "inc", "ru", "nl", "at", "ro", "uk", "co", "rs"]
    ]
    # Оставляем, например, до 3-х самых специфичных токенов (ближайших к основному домену)
    host_tokens = host_tokens[-3:]
    # Оставляем не более N самых специфичных токенов, например, 3-4 последних не-TLD частей
    # Пример: для "a.b.c.checks.edadeal.yandex.ru" можно взять ["checks", "edadeal", "yandex"]
    # или даже только ["checks", "edadeal"] если "yandex" слишком общий.
    # Для простоты пока возьмем все отфильтрованные.
    # Можно добавить логику для отсечения общих (типа "yandex", "google") если они не являются основной частью.
    # Для "checks.edadeal.yandex.ru" -> host_tokens = ["checks", "edadeal", "yandex"]
    
    if not host_tokens:
        return core_names

    # 2. Генерация на основе одиночных токенов хоста
    for token in host_tokens:
        # a) Токен + суффикс
        for suffix in TOKEN_SUFFIXES:
            core_names.add(f"{token}-{suffix}")
           # core_names.add(f"{token}_{suffix}") # Вариант с подчеркиванием
           # core_names.add(f"{token}{suffix.capitalize()}") # camelCase-подобный вариант

        # b) Префикс + токен
        for prefix in TOKEN_PREFIXES:
            core_names.add(f"{prefix}-{token}")
         #   core_names.add(f"{prefix}_{token}")
         #   core_names.add(f"{prefix}{token.capitalize()}")
            
        # c) Просто токен (если он достаточно длинный и не общий)
        if len(token) > 3: # Чтобы не добавлять "api", "dev" без всего
             core_names.add(token)

    # 3. Генерация на основе комбинации ДВУХ токенов хоста (если их >= 2)
    if len(host_tokens) >= 2:
        # Берем, например, два самых специфичных (последние не-TLD)
        # Для "checks.edadeal.yandex.ru", если host_tokens = ["checks", "edadeal", "yandex"]
        # токен_комбо1 = "checks", токен_комбо2 = "edadeal"
        # или все попарные комбинации
        
        for i in range(len(host_tokens)):
            for j in range(len(host_tokens)):
                if i == j:
                    continue
                
                token1 = host_tokens[i]
                token2 = host_tokens[j]
                
                # Основа: token1-token2
                combined_base = f"{token1}-{token2}"
                core_names.add(combined_base)
                core_names.add(f"{token1}_{token2}")
                core_names.add(f"{token1}{token2.capitalize()}")

                # Комбинированная основа + суффикс
                for suffix in TOKEN_SUFFIXES:
                    core_names.add(f"{combined_base}-{suffix}")
                    core_names.add(f"{combined_base}_{suffix}")
                    # core_names.add(f"{combined_base}{suffix.capitalize()}") # Может быть избыточно

                # Префикс + комбинированная основа
                for prefix in TOKEN_PREFIXES:
                    core_names.add(f"{prefix}-{combined_base}")
                    core_names.add(f"{prefix}_{combined_base}")
                    # core_names.add(f"{prefix}{combined_base.replace('-', '').capitalize()}")

    # 4. (Опционально) Более сложные комбинации или преобразования регистра - пока опустим для контроля количества

    return core_names

def format_as_http_header(core_name: str, wrapper_prefix: str = "X") -> str:
    # ... (код функции как в предыдущем ответе) ...
    if not core_name: # Проверка на пустую строку
        return ""
        
    parts = re.split(r'[-_]', core_name) 
    formatted_parts = []
    for part in parts:
        if not part: continue
        if part.isupper(): 
            formatted_parts.append(part)
        else:
            formatted_parts.append(part.capitalize())
    
    if not formatted_parts and core_name: 
        if core_name.isupper():
            formatted_name_part = core_name
        else:
            formatted_name_part = core_name.capitalize()
    elif formatted_parts:
        formatted_name_part = "-".join(formatted_parts)
    else: 
        return "" # Если core_name был пуст или только из разделителей

    if wrapper_prefix: # Если префикс не пустой
        return f"{wrapper_prefix}-{formatted_name_part}"
    else: 
        return formatted_name_part


# Основная функция, которую вы будете вызывать
def generate_all_contextual_headers(hostname: str, base_original_headers: list) -> list:
    # ... (код функции как в предыдущем ответе) ...
    # Убедимся, что base_original_headers это set для эффективности
    # и чтобы потом корректно посчитать количество добавленных
    # base_set = set(h.lower() for h in base_original_headers) # Приводим к нижнему регистру для сравнения
    base_set = set(base_original_headers) # Оставляем как есть, если не хотим менять регистр базовых

    core_names = generate_hostname_based_core_names(hostname)
    
    final_header_candidates = set()
    
    for core_name in core_names:
        if not core_name: continue

        for http_prefix in HTTP_HEADER_PREFIXES_WRAPPERS:
            # Генерируем канонический вид (X-Capitalized-Word)
            canonical_header = format_as_http_header(core_name, http_prefix)
            if canonical_header: # Убедимся, что что-то сгенерировалось
                final_header_candidates.add(canonical_header)
            
            # Генерируем вариант в нижнем регистре
            # (нормализация регистра в format_as_http_header уже делает капитализацию,
            # поэтому просто .lower() от канонического)
            if canonical_header: # Проверяем еще раз, т.к. format_as_http_header мог вернуть пустую строку
                final_header_candidates.add(canonical_header.lower())

        # Вариант без X- префикса, но канонизированный
        core_as_header = format_as_http_header(core_name, "") # Пустой префикс
        if core_as_header:
            final_header_candidates.add(core_as_header)
            final_header_candidates.add(core_as_header.lower())

    final_header_candidates.discard("") # Удаляем пустые строки, если они есть

    # Добавляем сгенерированные к базовому списку (уже как set для уникальности)
    # Не добавляем, если уже есть в base_set в любом регистре (сложнее)
    # Проще: пусть binary_search_group работает с чуть большим списком,
    # а серверная сторона нечувствительна к регистру.
    # Или, если хочется точной статистики, нужно сравнивать с base_set (приведенным к lower)
    
    # Просто объединяем. Дубликаты по точному совпадению уберет set.
    # Если ALL_HEADER_NAMES уже содержит X-My-Header, а мы генерируем X-My-Header, set это обработает.
    # Если ALL_HEADER_NAMES содержит x-my-header, а мы X-My-Header, они будут разными элементами в set.
    # Это нормально, так как при отправке заголовки обычно регистронезависимы.
    
    combined_headers = set(base_original_headers) # Начинаем с копии базового списка
    combined_headers.update(final_header_candidates)
        
    return list(combined_headers)

async def send_request(client: httpx.AsyncClient, url: str, headers: dict, retries=MAX_RETRIES):
    try:
        for attempt in range(retries):
            try:
                final_headers = {**headers, 'User-Agent': random.choice(USER_AGENTS)}
                resp = await asyncio.wait_for(
                    client.get(url, headers=final_headers, timeout=TIMEOUT, follow_redirects=False),
                    timeout=12.0
                )
                content = resp.content # Эта операция читает все тело ответа               
                await throttler.success()
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
            
            # Этот блок не будет достигнут при MAX_RETRIES = 1, если не было return или raise выше
            # try:
            #     delay = await throttler.delay() # Вернет фиксированное значение (например, 0.05)
            #     await asyncio.sleep(delay * (attempt + 1)) 
            # except asyncio.CancelledError:
            #     raise
                
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
        for element in soup.find_all(string=True):
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

async def content_similarity(a: str, b: str) -> float: # Ваша существующая функция
    ts_overall_start_cs = time.monotonic()
    operation_url_context = "" # Вы можете передать URL сюда для логирования, если нужно

    # 1. Нормализация
    ts_norm_start = time.monotonic()
    norm_a = await normalize_content(a) # normalize_content уже логирует свое время
    norm_b = await normalize_content(b)
    await log_time_taken(f"content_similarity: Normalization A+B", ts_norm_start, operation_url_context)

    # 2. Сравнение хешей НОРМАЛИЗОВАННОГО контента
    ts_hash_norm_start = time.monotonic()
    hash_norm_a = hashlib.sha256(norm_a.encode('utf-8', 'ignore')).hexdigest()
    hash_norm_b = hashlib.sha256(norm_b.encode('utf-8', 'ignore')).hexdigest()
    await log_time_taken(f"content_similarity: Hash normalized content", ts_hash_norm_start, operation_url_context)

    if hash_norm_a == hash_norm_b:
        await log_time_taken(f"content_similarity: TOTAL (via normalized hash match, orig lens: {len(a)}/{len(b)})", ts_overall_start_cs, operation_url_context)
        return 1.0 # Идентичны после нормализации

    # 3. Если хеши нормализованных текстов разные, делаем fuzz.ratio с семплированием
    ts_fuzz_start = time.monotonic()
    SAMPLE_SIZE_FUZZ = 10000  # <--- Установите желаемый размер семпла (например, 10KB)
    
    norm_a_fuzz = norm_a
    if len(norm_a) > SAMPLE_SIZE_FUZZ:
        norm_a_fuzz = norm_a[:SAMPLE_SIZE_FUZZ // 2] + norm_a[-SAMPLE_SIZE_FUZZ // 2:]
    
    norm_b_fuzz = norm_b
    if len(norm_b) > SAMPLE_SIZE_FUZZ:
        norm_b_fuzz = norm_b[:SAMPLE_SIZE_FUZZ // 2] + norm_b[-SAMPLE_SIZE_FUZZ // 2:]

    text_similarity = fuzz.ratio(norm_a_fuzz, norm_b_fuzz) / 100
    await log_time_taken(f"content_similarity: fuzz.ratio (SAMPLE {SAMPLE_SIZE_FUZZ}, actual_lens: {len(norm_a_fuzz)}/{len(norm_b_fuzz)})", ts_fuzz_start, operation_url_context)
    
    # 4. DOM анализ (остается как есть)
    # extract_dom_structure уже логирует свое время, если оно значительно
    dom_a = extract_dom_structure(a) 
    dom_b = extract_dom_structure(b)
    
    dom_similarity_val = text_similarity 
    if dom_a and dom_b:
        ts_dom_match_start = time.monotonic()
        matcher = difflib.SequenceMatcher(None, dom_a, dom_b)
        dom_similarity_val = matcher.ratio()
        await log_time_taken(f"content_similarity: DOM SequenceMatcher (tag_counts: {len(dom_a)}/{len(dom_b)})", ts_dom_match_start, operation_url_context)
    
    # 5. Проверка ошибок (остается как есть, но лучше ее делать в compare_responses на оригинальных текстах)
    # Для чистоты content_similarity, эту проверку можно убрать отсюда,
    # так как compare_responses уже ее делает.
    # error_a = detect_error_patterns(a) 
    # error_b = detect_error_patterns(b)
    # if (error_a and not error_b) or (error_b and not error_a):
    #      await log_time_taken(f"content_similarity: TOTAL (via error mismatch)", ts_overall_start_cs, operation_url_context)
    #      return 0.0
            
    # 6. Итоговая схожесть (можно настроить веса, если DOM-анализ важен)
    # Например, если DOM сильно отличается, а текст похож, или наоборот.
    # Пока оставим простое усреднение.
    TEXT_WEIGHT_INTERNAL = 0.7 # Если хотите дать больший вес текстовой схожести
    DOM_WEIGHT_INTERNAL = 0.3  # Если хотите дать вес DOM схожести
    
    if dom_a or dom_b: # Если хотя бы для одного удалось извлечь DOM
        combined_similarity = (text_similarity * TEXT_WEIGHT_INTERNAL + dom_similarity_val * DOM_WEIGHT_INTERNAL)
    else: # Если DOM анализ не удался для обоих, полагаемся только на текст
        combined_similarity = text_similarity
    # Или ваша предыдущая логика:
    # combined_similarity = (text_similarity + dom_similarity_val) / 2


    await log_time_taken(f"content_similarity: TOTAL (orig lens: {len(a)}/{len(b)})", ts_overall_start_cs, operation_url_context)
    return combined_similarity

async def compare_responses(base_resp, test_resp):
    ts_compare_total_start = time.monotonic()
    operation_url_context = "" # Можете передать URL сюда, если нужно в логах log_time_taken

    if not base_resp or not test_resp:
        return 0.0, ["Response unavailable"]
    
    base_status, base_len, base_hash_raw, base_text, base_headers = base_resp
    test_status, test_len, test_hash_raw, test_text, test_headers = test_resp

    # 0. СУПЕР-БЫСТРАЯ ПРОВЕРКА: ХЕШИ СЫРОГО КОНТЕНТА, СТАТУС И ДЛИНА
    if base_hash_raw == test_hash_raw and base_status == test_status and base_len == test_len:
        await log_time_taken(f"compare_responses: TOTAL (via raw body hash,status,len match)", ts_compare_total_start, operation_url_context)
        return 1.0, [] 

    details = []
    similarity_components = []

    # 1. Сравнение статус-кодов
    status_similarity = 1.0 if base_status == test_status else 0.0
    similarity_components.append((status_similarity, STATUS_SIMILARITY_WEIGHT))
    if base_status != test_status:
        details.append(f"Status code changed: {base_status} → {test_status}")
        if abs(base_status // 100 - test_status // 100) >= 1: 
            similarity_components.append((0.0, 0.8)) 

    # 2. Сравнение длин контента
    length_diff = abs(base_len - test_len)
    # Учитываем test_len тоже в знаменателе, если base_len=0
    length_similarity = max(0, 1 - (length_diff / max(base_len, test_len, 1))) 
    similarity_components.append((length_similarity, LENGTH_SIMILARITY_WEIGHT))
    if length_diff > LENGTH_THRESHOLD:
        details.append(f"Content length changed: {base_len} → {test_len} (diff: {length_diff})")
        if length_diff > max(base_len, test_len) * 0.75: 
            similarity_components.append((0.0, 0.5))

    # 3. Сравнение контента (вызов вашей обновленной content_similarity)
    # content_similarity теперь сама содержит оптимизации с хешами нормализованного контента и семплированием
    ts_content_sim_call_start = time.monotonic()
    content_sim_score = await content_similarity(base_text, test_text) 
    await log_time_taken(f"compare_responses: Main content_similarity call", ts_content_sim_call_start, operation_url_context)
    
    similarity_components.append((content_sim_score, DOM_SIMILARITY_WEIGHT)) # DOM_SIMILARITY_WEIGHT теперь как вес для общего content_sim_score

    if content_sim_score < STRUCTURAL_THRESHOLD: 
         details.append(f"Content (text/DOM) changed significantly (overall similarity: {content_sim_score:.2f})")

    # 4. Проверка на рефлексию
    if COMMON_VALUE in test_text and COMMON_VALUE not in base_text:
        details.append("Value reflection detected")
        similarity_components.append((0.0, 0.5)) # Сильно понижаем схожесть
    
    # 5. Проверка на паттерны ошибок
    base_errors = detect_error_patterns(base_text) 
    test_errors = detect_error_patterns(test_text)
    if (base_errors and not test_errors) or (not base_errors and test_errors) or \
       (base_errors and test_errors and set(base_errors) != set(test_errors)):
        new_errors = list(set(test_errors) - set(base_errors))
        resolved_errors = list(set(base_errors) - set(test_errors))
        if new_errors: details.append(f"New error patterns: {', '.join(new_errors)}")
        if resolved_errors: details.append(f"Resolved error patterns: {', '.join(resolved_errors)}")
        similarity_components.append((0.0, 0.7)) 
    
    # 6. Различия в важных заголовках ответа
    important_headers = ['location', 'content-type', 'content-disposition']
    for header_name in important_headers:
        base_val = base_headers.get(header_name)
        test_val = test_headers.get(header_name)
        if base_val != test_val:
            details.append(f"Header '{header_name}' changed: {base_val} → {test_val}")
            similarity_components.append((0.0, 0.2))

    # Расчет итоговой взвешенной схожести
    weighted_similarity = 1.0 
    if similarity_components:
        total_weight = sum(weight for _, weight in similarity_components)
        if total_weight > 0:
            weighted_similarity = sum(sim_score * weight for sim_score, weight in similarity_components) / total_weight
        elif not any(sim_score < 1.0 for sim_score, _ in similarity_components):
             weighted_similarity = 1.0
        else: 
             weighted_similarity = 0.0 
    
    await log_time_taken(f"compare_responses: TOTAL", ts_compare_total_start, operation_url_context, f"final_sim={weighted_similarity:.2f}")
    return weighted_similarity, details

async def calibrate(client: httpx.AsyncClient, url: str):
    """Calibrate baseline response. If the first response is too large, skip full calibration."""
    results = []
    normalized_contents = []
    first_response_checked = False # Флаг для проверки первого ответа

    for i in range(CALIBRATION_ATTEMPTS):
        test_url = await append_cb(url)
        r = await send_request(client, test_url, {})
        if not r:
            await asyncio.sleep(0.5) # Небольшая пауза перед следующей попыткой, если запрос не удался
            continue

        status, length, hash_val, text, headers = r

        # Проверка размера первого успешного ответа
        if not first_response_checked:
            first_response_checked = True
            if length >= MAX_RESPONSE_SIZE_BYTES:
                await safe_print(f"{Fore.YELLOW}[DEBUG] calibrate: First response for {url} is too large ({length / (1024*1024):.2f} MB). Skipping full calibration, returning this single response for size check.{Style.RESET_ALL}")
                # Возвращаем этот первый ответ, чтобы process_url мог его проверить и пропустить хост
                # Мы не будем проводить полную калибровку схожести, т.к. хост все равно будет пропущен.
                return (status, length, hash_val, text, headers) # Возвращаем как есть

        # Если размер в норме или это не первый ответ (и мы решили продолжать), делаем полную обработку
        normalized = await normalize_content(text)
        normalized_contents.append(normalized)
        results.append((status, length, hash_val, text, headers))
        
        # Опционально: если уже собрали достаточно для "плохой" калибровки, но хотим быстрее
        # if i >= 2 and len(results) < 2: # Если после 3 попыток меньше 2 успешных - можно выйти
        #     await safe_print(f"{Fore.YELLOW}[DEBUG] calibrate: Not enough successful responses after {i+1} attempts for {url}.{Style.RESET_ALL}")
        #     break # Выходим из цикла раньше

        await asyncio.sleep(0.3) # Задержка между успешными запросами калибровки

    if not results: # Если вообще не было успешных запросов
        await safe_print(f"{Fore.YELLOW}[!] No successful responses during calibration for {url}{Style.RESET_ALL}")
        return None

    if len(results) < 2: # Нужно хотя бы 2 для сравнения, если мы дошли досюда
        await safe_print(f"{Fore.YELLOW}[!] Not enough calibration data (got {len(results)}) for {url} to perform similarity analysis. Using the first available response.{Style.RESET_ALL}")
        return results[0] # Возвращаем первый успешный, если их мало для анализа

    # Build similarity matrix
    similarity_matrix = []
    for i_norm in range(len(normalized_contents)):
        row = []
        for j_norm in range(len(normalized_contents)):
            # Для больших текстов fuzz.ratio может быть дорогим.
            # Можно добавить ограничение на длину строк для fuzz.ratio
            # MAX_FUZZ_LEN = 10000 # Например, 10KB
            # norm_a_fuzz = normalized_contents[i_norm][:MAX_FUZZ_LEN]
            # norm_b_fuzz = normalized_contents[j_norm][:MAX_FUZZ_LEN]
            # sim = fuzz.ratio(norm_a_fuzz, norm_b_fuzz) / 100
            sim = fuzz.ratio(normalized_contents[i_norm], normalized_contents[j_norm]) / 100
            row.append(sim)
        similarity_matrix.append(row)

    # Find most consistent response (highest average similarity to others)
    avg_similarities = [sum(row) / len(row) for row in similarity_matrix]
    best_idx = avg_similarities.index(max(avg_similarities))

    # Log calibration quality
    avg_sim = avg_similarities[best_idx]
    if avg_sim >= 0.95:
        quality_color = Fore.GREEN
        quality_text = "Excellent"
    elif avg_sim >= 0.9:
        quality_color = Fore.CYAN
        quality_text = "Good"
    elif avg_sim >= 0.8:
        quality_color = Fore.YELLOW
        quality_text = "Fair"
    else:
        quality_color = Fore.RED
        quality_text = "Poor"

    await safe_print(f"{quality_color}[+] Calibrated {url} - {quality_text} quality ({avg_sim:.2f}) based on {len(results)} responses.{Style.RESET_ALL}")

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
        #    async with asyncio.timeout(10):  # 10-секундный таймаут на запрос
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
                   #     async with asyncio.timeout(30):  # 5-секундный таймаут на одиночный запрос
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
           #             async with asyncio.timeout(30):  # 5-секундный таймаут на проверку влияния
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
    #        async with asyncio.timeout(5):  # 5-секундный таймаут на сравнение
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
 #                   async with asyncio.timeout(5):  # 5-секундный таймаут на проверку влияния
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
        return
    
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
        
   #     async with aiofiles.open('debug.log', 'a', encoding='utf-8') as f:
   #         await f.write(f"\n--- CACHE POISONING ANALYSIS ---\n")
    #        await f.write(json.dumps(analysis_log, indent=2, ensure_ascii=False))
    #        await f.write("\n--- END OF ANALYSIS ---\n\n")
        
        if is_poisoned:
            poisoning_results.append((path, is_poisoned, reason, verify_status, verify_length))
    
    return poisoning_results


# Modify the process_url function to include cache poisoning tests
async def process_url(url: str, ver_sem_arg: asyncio.Semaphore, pois_sem_arg: asyncio.Semaphore):
    task_id_process_url = id(asyncio.current_task())
    await safe_print(f"\n{Fore.MAGENTA}[~] Task {task_id_process_url}: START Processing host: {url}{Style.RESET_ALL}")
    """Process a single URL to find impactful headers."""
    await safe_print(f"\n{Fore.MAGENTA}[~] Processing host: {url}{Style.RESET_ALL}")
    start_time = time.time()
    
    domain = "" # Инициализируем domain
    try:
        parsed_url = urlparse(url)
        domain = parsed_url.netloc or url # Пытаемся извлечь netloc
        if not domain: # Если urlparse не смог извлечь netloc (например, для относительных URL или просто строки)
            # Попробуем извлечь хост из пути, если схема есть но нет netloc (редко)
            if parsed_url.scheme and parsed_url.path:
                 # Для "file:///example.com/path" path будет "/example.com/path"
                 # Для "http:example.com/path" path будет "example.com/path"
                 path_parts = parsed_url.path.lstrip('/').split('/')
                 if path_parts:
                     domain = path_parts[0]
            elif not parsed_url.scheme and not parsed_url.netloc and parsed_url.path: # Просто "example.com/path" или "example.com"
                 domain = parsed_url.path.split('/')[0]
            elif not domain and url: # Если все еще пусто, но URL не пустой
                 # Очень грубая попытка извлечь что-то похожее на домен
                 temp_domain = url.split('/')[0] if '/' in url else url
                 if '.' in temp_domain or temp_domain == "localhost": # Простое условие, что это может быть домен
                     domain = temp_domain

    except ValueError as e: # Ошибка парсинга URL
        await safe_print(f"{Fore.RED}[!] Invalid URL format for {url}: {str(e)}{Style.RESET_ALL}")
        await safe_write(RESULT_FILE, f"[!] Skipped invalid URL: {url} - Error: {str(e)}\n" + "="*50 + "\n")
        return
    
    if not domain: # Если домен все еще не определен после всех попыток
        await safe_print(f"{Fore.RED}[!] Could not determine domain for URL: {url}{Style.RESET_ALL}")
        await safe_write(RESULT_FILE, f"[!] Skipped URL (no domain for contextual generation): {url}\n" + "="*50 + "\n")
        return

    limits = httpx.Limits(
        max_connections=50, # Это хороший лимит для клиента, т.к. он используется для одного хоста
        max_keepalive_connections=30,
        keepalive_expiry=15.0
    )
    client = httpx.AsyncClient(http2=True, verify=False, limits=limits)
    active_tasks = []
    
    try:
        async with sem_hosts: # Семафор для ограничения одновременной обработки хостов
            try:
                async with asyncio.timeout(1000):  # Общий таймаут на всю обработку этого URL
                    # Step 1: Calibrate baseline response
                    base = None
                    try:
                        async with asyncio.timeout(30):  # Таймаут на калибровку
                            base = await calibrate(client, url)
                    except asyncio.TimeoutError:
                        await safe_print(f"{Fore.RED}[!] Calibration timed out for {url}{Style.RESET_ALL}")
                        return # client.aclose() будет в finally
                        
                    if not base:
                        await safe_print(f"{Fore.RED}[!] Calibration failed for {url}{Style.RESET_ALL}")
                        return # client.aclose() будет в finally
                    
                    base_status_check, base_len_check, _, base_text_for_size_check, _ = base # Добавил base_text_check для отладки размера, если нужно
                    if base_len_check >= MAX_RESPONSE_SIZE_BYTES:
                        skip_message_console = f"{Fore.YELLOW}[!] Skipping host {domain} ({url}) - initial response size ({base_len_check / (1024*1024):.2f} MB) exceeds 1MB limit.{Style.RESET_ALL}"
                        skip_message_file = f"[!] Skipped host {domain} ({url}) - initial response size ({base_len_check} bytes / {base_len_check / (1024*1024):.2f} MB) exceeds 1MB limit.\n" + "="*50 + "\n"
                        await safe_print(skip_message_console)
                        await safe_write(RESULT_FILE, skip_message_file)
                        return # client.aclose() будет в finally
                        
                    bs, bl, bh, _, base_headers = base # Используем переменные из base
                    content_type_base = base_headers.get('content-type', 'unknown') # Переименовал для ясности
                    await safe_print(f"{Fore.CYAN}[~] Baseline for {url}: [{bs}] CL:{bl} Type:{content_type_base}{Style.RESET_ALL}")
                    
                    # Step 2: Search for impactful headers
                    found_headers_list = [] # Убедись, что переменные инициализированы ДО try
                    header_reasons = {}   # на случай, если binary_search_group вызовет ошибку до присвоения

                    try:
                        async with asyncio.timeout(1000):  # Таймаут на весь процесс поиска заголовков
                            bm = BatchManager()
                            
                            if 'ALL_HEADER_NAMES' not in globals(): # Проверка что глобальный список загружен
                                await safe_print(f"{Fore.RED}[CRITICAL] ALL_HEADER_NAMES not loaded. Aborting for {url}.{Style.RESET_ALL}")
                                return # client.aclose() будет в finally

                            headers_to_test = generate_all_contextual_headers(domain, list(ALL_HEADER_NAMES)) 
                            random.shuffle(headers_to_test)

                            num_total_headers = len(headers_to_test)
                            num_base_in_generated = sum(1 for h_gen in headers_to_test if h_gen in ALL_HEADER_NAMES) # Сколько из базовых попало в итоговый список
                            num_contextual = num_total_headers - num_base_in_generated
                            
                            await safe_print(f"{Fore.BLUE}[i] For {domain} ({url}): Testing {num_total_headers} headers (approx. {num_contextual} new contextual){Style.RESET_ALL}")

                            # Эта функция заполнит found_headers_list и header_reasons
                            found_headers_list, header_reasons = await binary_search_group(client, bm, url, base, headers_to_test)
                    
                    except asyncio.TimeoutError:
                        # Этот блок выполняется, если binary_search_group не успел отработать за 1000 секунд
                        await safe_print(f"{Fore.RED}[!] Header search (binary_search_group) timed out for {url}{Style.RESET_ALL}")
                        # found_headers_list будет содержать то, что успело найтись до таймаута (может быть пустым)
                        # header_reasons также будет содержать то, что успело заполниться.
                        # Важно, что мы не делаем return здесь, а позволяем коду дойти до проверки ниже.

                    # ===> ВОТ ПРАВИЛЬНОЕ МЕСТО ДЛЯ ПРОВЕРКИ НА "ШУМНЫЙ" ХОСТ <===
                    # Эта проверка выполняется ПОСЛЕ попытки поиска заголовков,
                    # НЕЗАВИСИМО от того, был таймаут или нет.
                    if len(found_headers_list) >= 10:
                        noisy_host_message = (
                            f"[!] Host: {domain} ({url})\n"
                            f"    Found {len(found_headers_list)} or more impactful headers.\n"
                            f"    This host appears to be noisy or overly sensitive to custom headers.\n"
                            f"    Skipping detailed report and further tests for this host.\n"
                            + "="*50 + "\n"
                        )
                        await safe_print(f"{Fore.YELLOW}[!] For {url}: Found {len(found_headers_list)}+ headers. Host is noisy, skipping detailed report.{Style.RESET_ALL}")
                        await safe_write(RESULT_FILE, noisy_host_message)
                        
                        # Клиент будет закрыт в блоке finally функции process_url
                        return # ВЫХОДИМ ИЗ process_url, не идем к "Step 3"

                    # Step 3: Process and report results
                    # Этот код выполнится ТОЛЬКО ЕСЛИ найдено МЕНЕЕ 10 заголовков
                    lines = []
                    reportable_headers_count = 0 # Счетчик для заголовков, о которых мы сообщаем (включая таймауты)

                    cache_poisoning_results = {}

                    if found_headers_list:
                        lines.append(f"[+] Results for {domain} ({url}):")

                        headers_for_verification = []
                        # Сначала обрабатываем и добавляем в отчет те, что вызвали таймаут или таймаут верификации
                        for hdr in found_headers_list:
                            reason = header_reasons.get(hdr, "Unknown reason")
                            if "timeout" in reason.lower(): # "Caused timeout" или "Verification timed out"
                                lines.append(f"  {hdr} => {reason}")
                                reportable_headers_count += 1
                            else:
                                headers_for_verification.append(hdr) # Эти пойдут на детальную верификацию
                        
                        # Если уже набрали 10 (или более) "проблемных" заголовков (включая таймауты),
                        # можем решить не проводить дальнейшую верификацию или тесты кеша.
                        if reportable_headers_count >= 10:
                            await safe_print(f"{Fore.CYAN}[!] For {url}: Found {reportable_headers_count} headers (incl. timeouts). Skipping further detailed verification and cache poisoning tests.{Style.RESET_ALL}")
                            # headers_for_verification останутся пустыми или не будут обработаны дальше
                            headers_for_verification = [] # Очищаем, чтобы не запускать gather
                        
                        # Верификация заголовков, которые не вызвали таймаут на этапе поиска
                        verification_tasks = []
                        if headers_for_verification: # Только если есть что верифицировать и лимит не достигнут
                            for hdr_verify in headers_for_verification:
                                task = asyncio.create_task(verify_single_header_with_sem(ver_sem_arg, client, url, hdr_verify, base))
                                verification_tasks.append(task)
                                active_tasks.append(task)
                        
                        verification_results = []
                        if verification_tasks:
                            try:
                                async with asyncio.timeout(120): # Таймаут на все задачи верификации
                                    verification_results = await asyncio.gather(*verification_tasks)
                            except asyncio.TimeoutError:
                                await safe_print(f"{Fore.RED}[!] Verification phase (asyncio.gather) timed out for {url}{Style.RESET_ALL}")
                                # Помечаем все не завершившиеся задачи верификации как таймаутнутые
                                for i, task_v in enumerate(verification_tasks):
                                    if not task_v.done():
                                        task_v.cancel()
                                        # Обновляем 'lines' для этого заголовка или добавляем, если его еще нет
                                        hdr_timed_out = headers_for_verification[i]
                                        # Удаляем предыдущую запись если она была (маловероятно, но для чистоты)
                                        # lines = [l for l in lines if not l.strip().startswith(f"{hdr_timed_out} =>")]
                                        lines.append(f"  {hdr_timed_out} => Verification process timed out for this header")
                                        reportable_headers_count +=1 


                        # Обработка результатов верификации
                        successfully_verified_impactful_headers = []
                        for i, verification_data in enumerate(verification_results):
                            if i < len(headers_for_verification): # Убедимся, что индекс в пределах
                                hdr_verified = headers_for_verification[i]
                                if verification_data: # Если результат не None (не отменена задача без результата)
                                    status, length, content_type_res, details = verification_data
                                    lines.append(f"  {hdr_verified} => [{status}] CL:{length} Type:{content_type_res}")
                                    if details:
                                        lines.append(f"    Details: {details}")
                                    reportable_headers_count +=1 # Считаем как еще один сообщаемый заголовок
                                    # Для теста на отравление кеша нам нужны те, что не "TIMEOUT" и не "No consistent impact detected"
                                    # или любая другая логика, определяющая "действительно влияющий"
                                    if status != "TIMEOUT" and "No consistent impact detected" not in details and "No significant change" not in details:
                                        successfully_verified_impactful_headers.append(hdr_verified)
                                # Если verification_data is None (например, gather прервался и задача была отменена), мы уже обработали выше
                        
                        # Тестирование на отравление кеша
                        cache_poisoning_results = {}
                        # Тестируем только ограниченное количество успешно верифицированных и влияющих заголовков
                        headers_for_cache_test = successfully_verified_impactful_headers

                        poisoning_tasks = []
                        # Запускаем тесты на отравление только если общее количество найденных заголовков не слишком велико
                        if headers_for_cache_test and reportable_headers_count < 10:
                            for hdr_poison in headers_for_cache_test:
                                task = asyncio.create_task(test_cache_poisoning_with_sem(pois_sem_arg, client, url, hdr_poison, base))
                                poisoning_tasks.append(task)
                                active_tasks.append(task)
                        
                        poisoning_results_gathered = []
                        if poisoning_tasks:
                            try:
                                async with asyncio.timeout(180): # Таймаут на все тесты отравления
                                    poisoning_results_gathered = await asyncio.gather(*poisoning_tasks)
                            except asyncio.TimeoutError:
                                await safe_print(f"{Fore.RED}[!] Cache poisoning tests (asyncio.gather) timed out for {url}{Style.RESET_ALL}")
                                for task_p in poisoning_tasks:
                                    if not task_p.done(): task_p.cancel()
                        
                        # Обработка результатов отравления кеша
                        if poisoning_results_gathered:
                            lines.append(f"\n[~] Cache Poisoning Tests:")
                            for i, poisoning_data_list in enumerate(poisoning_results_gathered):
                                if i < len(headers_for_cache_test):
                                    hdr_p_test = headers_for_cache_test[i]
                                    if poisoning_data_list: # Это список результатов от test_cache_poisoning
                                        cache_poisoning_results[hdr_p_test] = poisoning_data_list
                                        await safe_print(f"{Fore.RED}[!] CACHE POISONING detected with header: {hdr_p_test} for {url}{Style.RESET_ALL}")
                                        lines.append(f"  [!] CACHE POISONING with header: {hdr_p_test}")
                                        for path, is_poisoned, reason_cp, status_cp, length_cp in poisoning_data_list:
                                            if is_poisoned:
                                                lines.append(f"    - Path: {path} - [{status_cp}] CL:{length_cp}")
                                                lines.append(f"      {reason_cp}")
                                    else:
                                        lines.append(f"  [-] No cache poisoning found with header: {hdr_p_test}")
                    
                    else: # Если found_headers_list пуст
                        lines.append(f"[+] No impactful headers found for {domain} ({url})")
                    
                    elapsed_url = time.time() - start_time
                    lines.append(f"[i] Scan for {url} completed in {elapsed_url:.2f} seconds")
                    
                    if cache_poisoning_results:
                        vulnerable_paths = set()
                        for _hdr, results_list in cache_poisoning_results.items():
                            for path, is_poisoned, _, _, _ in results_list:
                                if is_poisoned:
                                    vulnerable_paths.add(path)
                        
                        if vulnerable_paths:
                            lines.append(f"\n[!!!] CACHE POISONING VULNERABILITY SUMMARY for {url}:")
                            lines.append(f"  Host: {domain}")
                            lines.append(f"  Vulnerable paths: {', '.join(vulnerable_paths)}")
                            lines.append(f"  Exploitable headers: {', '.join(cache_poisoning_results.keys())}")
                            lines.append(f"  Recommendation: This server appears vulnerable to cache poisoning attacks.")
                    
                    block = "\n".join(lines) + "\n" + "="*50 + "\n"
                    await safe_print(block)
                    await safe_write(RESULT_FILE, block)
                    
            except asyncio.TimeoutError: # От общего asyncio.timeout(600)
                await safe_print(f"{Fore.RED}[!] Complete processing for {url} timed out after {time.time() - start_time:.2f}s{Style.RESET_ALL}")
                await safe_write(RESULT_FILE, f"[!] Processing timed out for {url} after {time.time() - start_time:.2f}s\n" + "="*50 + "\n")
                
    except Exception as e:
        await safe_print(f"{Fore.RED}[!] Critical error processing {url}: {str(e)}{Style.RESET_ALL}")
        logger.error(f"Critical error processing {url}", exc_info=True) # Логируем с трассировкой
        await safe_write(RESULT_FILE, f"[!] CRITICAL Error processing {url}: {str(e)}\n" + "="*50 + "\n")
        
    finally:
        for task in active_tasks:
            if not task.done():
                task.cancel()
        # Собираем мусор только если много активных задач было, или периодически
        if len(active_tasks) > 20: # Пример условия
            import gc
            gc.collect()
        
        try:
            if client and not client.is_closed: # Проверяем, что клиент существует и не закрыт
                await client.aclose()
        except Exception as e_close:
            await safe_print(f"{Fore.RED}[!] Error closing client for {url}: {str(e_close)}{Style.RESET_ALL}")

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
    global ALL_HEADER_NAMES # Убедитесь, что эта переменная объявлена глобально и загружается
   # global verification_sem, poisoning_sem # Семафоры тоже глобальные
    local_verification_sem = asyncio.Semaphore(15)
    local_poisoning_sem = asyncio.Semaphore(5)

    # Создаем глобальные семафоры для всего приложения (если они еще не созданы где-то выше)
    # Если они уже созданы глобально, эту часть можно пропустить.
    # Для примера предполагаем, что они определены глобально.
    # verification_sem = asyncio.Semaphore(15)
    # poisoning_sem = asyncio.Semaphore(5)
    
    # ... (код загрузки URLS_FILE, HEADERS_FILE, валидации, инициализации RESULT_FILE, начальные принты) ...
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
    
    urls = await validate_urls(raw_urls)
    
    if not urls:
        await safe_print(f"{Fore.RED}[!] Error: No valid URLs to scan{Style.RESET_ALL}")
        return
    
    open(RESULT_FILE, 'w').close()
    
    await safe_print(f"{Fore.GREEN}[+] Starting Param Miner style header scan{Style.RESET_ALL}")
    await safe_print(f"{Fore.GREEN}[+] Loaded {len(ALL_HEADER_NAMES)} headers and {len(urls)} URLs (filtered from {len(raw_urls)}){Style.RESET_ALL}")
    await safe_print(f"{Fore.GREEN}[+] Using enhanced content similarity analysis{Style.RESET_ALL}")
    await safe_print(f"{Fore.GREEN}[+] Similarity threshold: {SIMILARITY_THRESHOLD}{Style.RESET_ALL}")
    
    # Process URLs with improved task management
    start_time_main = time.monotonic() # Используем monotonic для измерения общего времени
    
    batch_size = 40 
    all_tasks_global = [] # Переименовал для ясности, это все задачи со всех батчей

    for i_batch_loop_idx in range(0, len(urls), batch_size):
        current_batch_urls = urls[i_batch_loop_idx : i_batch_loop_idx + batch_size]
        await safe_print(f"{Fore.CYAN}[+] Processing batch {i_batch_loop_idx//batch_size + 1}/{(len(urls)+batch_size-1)//batch_size} ({len(current_batch_urls)} URLs){Style.RESET_ALL}")
        
        tasks_in_current_batch = []
        for u in current_batch_urls:
            task = asyncio.create_task(process_url(u, local_verification_sem, local_poisoning_sem)) 
            tasks_in_current_batch.append(task)
            all_tasks_global.append(task) # Добавляем в глобальный список для финальной отмены
        
        # ========== НАЧАЛО ИЗМЕНЕНИЙ ==========
        if tasks_in_current_batch: # Только если в батче есть задачи
            try:
                # Устанавливаем таймаут на обработку всего текущего батча
                # (450 секунд = 7.5 минут, как было у вас ранее)
                # Если вы хотите убрать таймаут на батч, закомментируйте 'async with asyncio.timeout(...):'
                # и оставьте только 'await asyncio.gather(...)'.
                async with asyncio.timeout(450): 
                    # Запускаем все задачи батча параллельно и ждем их завершения
                    # return_exceptions=True означает, что gather не упадет при первом исключении,
                    # а соберет все результаты и исключения.
                    batch_results = await asyncio.gather(*tasks_in_current_batch, return_exceptions=True)
                
                # Опционально: обработка результатов/исключений из batch_results, если нужно
                for idx, result_or_exc in enumerate(batch_results):
                    original_url_for_task = current_batch_urls[idx] # Получаем URL для контекста
                    if isinstance(result_or_exc, asyncio.CancelledError):
                        await safe_print(f"{Fore.YELLOW}[!] Task for {original_url_for_task} in batch was cancelled (possibly by batch timeout).{Style.RESET_ALL}")
                    elif isinstance(result_or_exc, Exception):
                        await safe_print(f"{Fore.RED}[!] Task for {original_url_for_task} in batch failed with: {type(result_or_exc).__name__} - {str(result_or_exc)}{Style.RESET_ALL}")
                    # Если все хорошо, то process_url сама напечатала свой отчет. Здесь ничего делать не нужно.

            except asyncio.TimeoutError: # Этот TimeoutError от async with asyncio.timeout(450) на батч
                await safe_print(f"{Fore.RED}[!] Batch {i_batch_loop_idx//batch_size + 1} processing timed out. Cancelling remaining tasks in this batch.{Style.RESET_ALL}")
                # Отменяем все еще не завершенные задачи из текущего батча
                for task_in_batch in tasks_in_current_batch:
                    if not task_in_batch.done():
                        task_in_batch.cancel()
                        # Даем шанс отмене завершиться, но не ждем ее результата здесь
                        try:
                            await asyncio.wait_for(task_in_batch, timeout=1.0) # Короткое ожидание отмены
                        except (asyncio.TimeoutError, asyncio.CancelledError):
                            pass # Игнорируем таймаут/отмену здесь
            except Exception as e_batch: # Другие возможные ошибки на уровне обработки батча
                await safe_print(f"{Fore.RED}[!] Error processing batch {i_batch_loop_idx//batch_size + 1}: {str(e_batch)}{Style.RESET_ALL}")
        # ========== КОНЕЦ ИЗМЕНЕНИЙ ==========
        
        await safe_print(f"{Fore.GREEN}[OK] Batch {i_batch_loop_idx//batch_size + 1} processing attempt finished.{Style.RESET_ALL}")
        if i_batch_loop_idx + batch_size < len(urls):
            await asyncio.sleep(15)
        
        # VVVVVV ЭТОТ БЛОК ТЕПЕРЬ БОЛЕЕ АКТУАЛЕН VVVVVV
        pending_tasks = [t for t in tasks_in_current_batch if not t.done()] # Используем tasks_in_current_batch
        if pending_tasks:
            await safe_print(f"{Fore.YELLOW}[!] Batch {i_batch_loop_idx//batch_size + 1}: {len(pending_tasks)} tasks still pending after nominal completion. Waiting/Cancelling...{Style.RESET_ALL}")
            # Предоставляем дополнительное время для завершения (опционально, можно сразу отменять)
            # for _ in range(5): 
            #     if not any(not t.done() for t in tasks_in_current_batch):
            #         break
            #     await asyncio.sleep(1)
            
            # Принудительно отменяем все оставшиеся в этом батче
            for task_to_cancel in tasks_in_current_batch: # Используем tasks_in_current_batch
                if not task_to_cancel.done():
                    task_to_cancel.cancel()
                    # Можно добавить небольшое ожидание здесь, чтобы дать шанс отмене пройти
                    try:
                        await asyncio.wait_for(task_to_cancel, timeout=1.0)
                    except (asyncio.TimeoutError, asyncio.CancelledError):
                        pass # Игнорируем, если отмена заняла >1с или уже была отменена
        
        import gc
        gc.collect()


    elapsed_main = time.monotonic() - start_time_main
    completion_message = f"\n{Fore.GREEN}Scan completed in {elapsed_main:.2f} seconds.{Style.RESET_ALL}"
    await safe_print(completion_message)
    await safe_write(RESULT_FILE, f"Scan completed in {elapsed_main:.2f} seconds.\n")

if __name__ == '__main__':
    asyncio.run(main())