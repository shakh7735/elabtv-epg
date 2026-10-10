"""Гиды программы для внешних плейлистов ElabTV: на каждый список каналов из lists/ — свой XMLTV.

Внешние (провайдерские) плейлисты идут без tvg-id, и приложение связывает их с гидом только по
названию. Полный гид источника на это не рассчитан: одно имя носят разные каналы, у части
каналов программы нет, а для «+2» нашлась бы московская сетка. Поэтому приложение само кладёт
сюда названия каналов своего плейлиста (lists/<отпечаток>.txt), а здесь для каждого названия
подбирается программа из всех источников sources.json. На выходе id и название канала — ровно
те, что в плейлисте: приложение находит канал без угадывания.

Как подбирается программа (по порядку):
  1. Каналы источников с тем же названием — по тем же правилам, что и в приложении (регистр,
     пробелы и пометки качества не важны). «+N» и «+» в названии должны совпасть: «НТВ +2» не
     получит московский НТВ, «ETV+» — программу «ETV».
  2. Название без города в скобках: «НТВ +4 (Алтай)» → «НТВ +4».
  3. «+N», которого нет ни в одном источнике, — основной канал со сдвигом на N часов; «+0 (Город)»
     — московская сетка.
Из подходящих выигрывает основной источник, если у него передача на сейчас есть и программы
хватает на ENOUGH_AHEAD вперёд; иначе — совпало ли главное название канала, а не псевдоним, и
чья программа длиннее. Ошибся подбор — явная строка в map.json: {"название": [источник, id]}
или [источник, id, сдвиг в часах]; null — оставить канал без программы.

  python3 tools/build.py [папка-для-скачанного] [папка-для-гидов]

Рядом с каждым гидом пишется <отпечаток>.txt — какой канал откуда получил программу. Списки,
про которые приложения не вспоминали дольше STALE (строка «# seen:»), удаляются вместе с гидом.

Без зависимостей: стандартная библиотека Python 3.9+.
"""
import datetime as dt
import gzip
import json
import os
import re
import shutil
import subprocess
import sys
import urllib.request
import xml.etree.ElementTree as ET

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LISTS = os.path.join(ROOT, "lists")
SOURCES = json.load(open(os.path.join(ROOT, "sources.json"), encoding="utf-8"))
MAP_FILE = os.path.join(ROOT, "map.json")
OVERRIDES = json.load(open(MAP_FILE, encoding="utf-8")) if os.path.exists(MAP_FILE) else {}
CACHE = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, ".cache")
OUT = sys.argv[2] if len(sys.argv) > 2 else os.path.join(ROOT, ".cache", "out")

NOW = dt.datetime.now(dt.timezone.utc)
# Неделя назад — вся глубина записи
BACK = NOW - dt.timedelta(hours=168)
# Основной источник годен, если программы на канал хватает хотя бы на столько вперёд
ENOUGH_AHEAD = dt.timedelta(hours=12)
MAX_DESC = 400
# Описания у прошедших передач — только за последние сутки. Внешние плейлисты — это тысячи
# каналов, и неделя записи с описаниями — триста мегабайт XML, которые приставке разбирать;
# в записи неделю назад ищут по названиям
DESC_SINCE = NOW - dt.timedelta(hours=24)
# Список, о котором приложения столько не напоминали, никому не нужен
STALE = dt.timedelta(days=30)
# Ссылку на запись в репозиторий знает каждый apk — потолки от мусора
MAX_LISTS = 100
MAX_NAMES = 6000
MAX_NAME_LENGTH = 200
LIST_NAME = re.compile(r"^[0-9a-f]{16}\.txt$")

QUALITY = ("hevc", "uhd", "fhd", "hdr", "hd", "sd", "4k", "orig")
# «+N» отдельным словом: «НТВ +2», «НТВ (+2)», но не «1+1»
SHIFT = re.compile(r"(?:^|\s)\(?\+\s*(\d{1,2})\s*\)?(?=\s|$)")


def norm(name):
    """Как normalizeChannelName в ElabTvCore, плюс пометка HDR («BCU Action HDR» = «BCU Action HD»)."""
    words = [w for w in re.split(r"[^\w]+|_", name.lower().replace("ё", "е")) if w]
    letters = "".join(w for w in words if w not in QUALITY) or "".join(words)
    for mark in QUALITY:
        if len(letters) > len(mark) and letters.endswith(mark):
            return letters[: -len(mark)]
    return letters


def shift_of(name):
    """Сдвиг эфира из названия: «Пятница! +4» → 4, «НТВ +0 (Тамбов)» → 0, без сдвига — None."""
    m = SHIFT.search(name)
    return int(m.group(1)) if m else None


def has_plus(name):
    """«+» без цифры — часть названия: «ETV+», «Setanta Sports+» — другие каналы, не «ETV»."""
    return bool(re.search(r"\+(?!\s*\d)", name))


def without_city(name):
    """«НТВ +4 (Алтай)» → «НТВ +4»: город в скобках есть у региональных вставок, в гидах — редко."""
    return re.sub(r"\s*\([^)]*\)\s*$", "", name)


def base_name(name):
    return SHIFT.sub(" ", without_city(name)).strip()


def parse_time(value):
    value = (value or "").strip()
    d = dt.datetime.strptime(value[:14].ljust(14, "0"), "%Y%m%d%H%M%S")
    zone = value[14:].strip() or "+0000"
    sign = 1 if zone[0] == "+" else -1
    return (d - sign * dt.timedelta(hours=int(zone[1:3]), minutes=int(zone[3:5]))).replace(tzinfo=dt.timezone.utc)


def fmt(t):
    return t.strftime("%Y%m%d%H%M%S +0000")


def coverage(programmes):
    """(есть ли передача на сейчас, до какого момента программа)."""
    if not programmes:
        return False, BACK
    on_air = any(s <= NOW < e for s, e, _, _ in programmes)
    return on_air, max(e for _, e, _, _ in programmes)


def download(name, url):
    """Через curl, если он есть: сам ходит по редиректам и берёт системные сертификаты."""
    os.makedirs(CACHE, exist_ok=True)
    path = os.path.join(CACHE, f"{name}.xml.gz")
    agent = "Mozilla/5.0 (ElabTV EPG builder)"
    if shutil.which("curl"):
        subprocess.run(["curl", "-sSfL", "--retry", "3", "-m", "900", "-A", agent, "-o", path + ".part", url], check=True)
    else:
        req = urllib.request.Request(url, headers={"User-Agent": agent})
        with urllib.request.urlopen(req, timeout=900) as resp, open(path + ".part", "wb") as out:
            while chunk := resp.read(1 << 20):
                out.write(chunk)
    os.replace(path + ".part", path)
    return path


def read_lists():
    """{отпечаток: [названия]} — свежие списки; устаревшие и битые удаляются здесь же."""
    lists = {}
    files = sorted((f for f in os.listdir(LISTS) if f.endswith(".txt")),
                   key=lambda f: os.path.getmtime(os.path.join(LISTS, f)), reverse=True)
    for name in files:
        path = os.path.join(LISTS, name)
        lines = open(path, encoding="utf-8-sig", errors="replace").read().splitlines()
        seen = next((l.split(":", 1)[1].strip() for l in lines if l.startswith("# seen:")), "")
        try:
            fresh = NOW - dt.datetime.fromisoformat(seen).replace(tzinfo=dt.timezone.utc) < STALE
        except ValueError:
            fresh = False
        # Служебная только «# seen:» — с «#» начинаются и названия каналов («#dabeiTV HD DE»)
        names = [l.strip()[:MAX_NAME_LENGTH] for l in lines if l.strip() and not l.startswith("# seen:")]
        if not LIST_NAME.match(name) or not fresh or not names or len(lists) >= MAX_LISTS:
            print(f"удаляю список {name}: {'устарел' if fresh is False else 'не подходит'}")
            os.remove(path)
            continue
        lists[name[:-4]] = list(dict.fromkeys(names))[:MAX_NAMES]
    return lists


def read_source(path, wanted_names, wanted_ids):
    """Названия всех каналов источника и программа тех, что подходят по названию или названы явно.

    Блоки <channel> в XMLTV идут раньше передач, поэтому нужные id известны к первой передаче.
    """
    channels = {}  # id → {"names": [...], "icon": ...}
    programmes = {}
    keep = None
    with gzip.open(path, "rb") as raw:
        for _, el in ET.iterparse(raw, events=("end",)):
            if el.tag == "channel":
                icon = el.find("icon")
                channels[el.get("id")] = {
                    "names": [(n.text or "").strip() for n in el.findall("display-name") if (n.text or "").strip()],
                    "icon": icon.get("src") if icon is not None else "",
                }
                el.clear()
            elif el.tag == "programme":
                if keep is None:
                    keep = {cid for cid, ch in channels.items()
                            if cid in wanted_ids or any(norm(n) in wanted_names for n in ch["names"])}
                cid = el.get("channel")
                if cid in keep:
                    try:
                        start, stop = parse_time(el.get("start")), parse_time(el.get("stop"))
                    except (ValueError, IndexError, TypeError):
                        start = stop = None
                    if start and stop > start and stop >= BACK:
                        title = (el.findtext("title") or "").strip()
                        desc = (el.findtext("desc") or "").strip()[:MAX_DESC]
                        programmes.setdefault(cid, []).append((start, stop, title, desc))
                el.clear()
    for items in programmes.values():
        items.sort()
    return channels, programmes


def rank(programmes, src, main):
    """Чем больше, тем лучше. Основной источник с передачей на сейчас и запасом вперёд выигрывает
    сразу: запасной по одному названию может оказаться другим каналом («Звезда» в iptvx —
    псевдоним «Звезды Плюс»). Дальше — совпало ли главное название, а не псевдоним, и чья
    программа длиннее."""
    on_air, until = coverage(programmes)
    primary = src == SOURCES["primary"]
    return (primary and on_air and until >= NOW + ENOUGH_AHEAD, on_air, main, until, len(programmes), primary)


def shifted(programmes, hours):
    delta = dt.timedelta(hours=hours)
    return [(s + delta, e + delta, t, d) for s, e, t, d in programmes]


def same_channel(playlist_name, guide_name):
    """Название из гида подходит каналу плейлиста: та же нормализация, тот же сдвиг и «+»."""
    return (norm(guide_name) == norm(playlist_name)
            and (shift_of(guide_name) or 0) == (shift_of(playlist_name) or 0)
            and has_plus(guide_name) == has_plus(playlist_name))


def pick(name, sources):
    """(программа, иконка, откуда) для канала плейлиста; программы нет — (None, "", причина)."""
    best = None
    for src, (channels, programmes) in sources.items():
        for cid, ch in channels.items():
            if cid not in programmes:
                continue
            names = ch["names"]
            hits = [n for n in names if same_channel(name, n)]
            if not hits:
                continue
            r = rank(programmes[cid], src, hits[0] == names[0])
            if best is None or r > best[0]:
                best = (r, programmes[cid], ch["icon"], f"{src}:{cid} {names[0]}")
    if best is not None:
        return best[1], best[2], best[3]
    if without_city(name) != name:
        found = pick(without_city(name), sources)
        if found[0]:
            return found
    hours = shift_of(name)
    if hours is not None and base_name(name) != name:
        base = pick(base_name(name), sources)
        if base[0]:
            label = f"{base[2]} со сдвигом +{hours} ч" if hours else f"{base[2]} (+0)"
            return shifted(base[0], hours), base[1], label
    return None, "", "нет в источниках"


def resolve(name, sources):
    if name in OVERRIDES:
        target = OVERRIDES[name]
        if target is None:
            return None, "", "выключено в map.json"
        channels, programmes = sources[target[0]]
        items = programmes.get(target[1], [])
        if len(target) > 2:
            items = shifted(items, target[2])
        return items or None, channels.get(target[1], {}).get("icon", ""), f"map {target[0]}:{target[1]}"
    return pick(name, sources)


def write_guide(key, names, sources):
    chosen, report = {}, []
    for name in names:
        entry = resolve(name, sources)
        if entry[0]:
            chosen[name] = entry
        report.append((name, entry[2], entry[0]))

    tv = ET.Element("tv", {"generator-info-name": "ElabTV EPG (внешний плейлист)"})
    for name, (_, icon, _) in chosen.items():
        ch = ET.SubElement(tv, "channel", {"id": name})
        ET.SubElement(ch, "display-name", {"lang": "ru"}).text = name
        if icon:
            ET.SubElement(ch, "icon", {"src": icon})
    for name, (items, _, _) in chosen.items():
        for start, stop, title, desc in items:
            p = ET.SubElement(tv, "programme", {"start": fmt(start), "stop": fmt(stop), "channel": name})
            ET.SubElement(p, "title", {"lang": "ru"}).text = title or "Без названия"
            if desc and stop >= DESC_SINCE:
                ET.SubElement(p, "desc", {"lang": "ru"}).text = desc

    os.makedirs(OUT, exist_ok=True)
    out = os.path.join(OUT, f"{key}.xml.gz")
    body = ET.tostring(tv, encoding="utf-8", xml_declaration=True)
    with open(out, "wb") as raw, gzip.GzipFile(fileobj=raw, mode="wb", mtime=0) as gz:
        gz.write(body)

    lines, with_now = [], 0
    for name, label, items in report:
        on_air, until = coverage(items or [])
        with_now += on_air
        state = "нет программы" if not items else ("сейчас есть" if on_air else "сейчас дыра")
        lines.append(f"{name}\t{state}\t{until:%d.%m %H:%M}\t{label}" if items else f"{name}\t{state}\t\t{label}")
    summary = (f"{key}: каналов {len(names)}, с программой {len(chosen)}, с передачей сейчас {with_now}; "
               f"{os.path.getsize(out) / 1e6:.1f} МБ")
    with open(os.path.join(OUT, f"{key}.txt"), "w", encoding="utf-8") as f:
        f.write(f"# {summary}\n# собрано {NOW:%Y-%m-%d %H:%M} UTC\n" + "\n".join(lines) + "\n")
    print(summary, flush=True)


def main():
    lists = read_lists()
    if not lists:
        print("списков нет")
        return
    wanted_names = set()
    for names in lists.values():
        for name in names:
            wanted_names.update((norm(name), norm(without_city(name)), norm(base_name(name))))
    wanted_ids = {}
    for target in OVERRIDES.values():
        if target:
            wanted_ids.setdefault(target[0], set()).add(target[1])
    sources = {}
    for src, url in SOURCES["sources"].items():
        print(f"{src}: качаю и разбираю…", flush=True)
        sources[src] = read_source(download(src, url), wanted_names, wanted_ids.get(src, set()))
    for key, names in lists.items():
        write_guide(key, names, sources)


if __name__ == "__main__":
    main()
