"""Server minimo di skydo (Render): una sola partita in memoria, condotta da chi conosce HOST_KEY.

POST /msg                   messaggio dei telefoni {id, name, emoji?, type: join|answer, answer} -> {seq, domanda, emoji}
                            name = nickname (anche ripetuto); il giocatore è riconosciuto dall'emoji, unica nella partita
                            409 se: emoji finite, domanda non partita, tempo scaduto, già risposto a questa domanda
GET  /msg?since=N&key=K     {epoch, boot, messages, restanti}: messaggi con seq > N e secondi rimasti, solo conduttore
GET  /classifica?id=X       {domanda in corso, giocatori, top: primi 3 (podio), me: riga di X}, pubblica
GET  /attesa?n=N            {domanda in corso} appena non è più la N (long-polling, max WAIT s), pubblica
                            domanda in corso = {n, round, manche, scelte, opzioni, restanti, soluzione?}: testi delle opzioni,
                            scelte = quante (0 = risposta aperta), restanti = secondi alla fine del tempo; solo a tempo
                            scaduto soluzione = risposta giusta e me.esito = {risposto, corretta, punti} della domanda.
                            Mentre il tempo corre, me.punti non conta la domanda in corso (il telefono non svela l'esito)
GET  /quiz?key=K            domande e risposte, solo conduttore
POST /login | /question | /reset   {"key": K[, "n": domanda]}: verifica chiave, avvia domanda, azzera la partita
`epoch` cambia a ogni reset o riavvio, così il conduttore sa che la numerazione è ripartita; `boot` solo al riavvio,
così distingue un riavvio (riprende la partita) da un reset fatto da un'altra pagina del conduttore (riparte da zero).
Tempo: `tempo` secondi dal via (default DEFAULT_TIME), poi le risposte sono rifiutate (409 timeout); `restanti` lo dice ai telefoni.
Punti: risposta giusta = da MAX_POINTS (subito) a MIN_POINTS (allo scadere del tempo), sbagliata = 0.
Correttezza da quiz.json (Secret File di Render, mai nel repo pubblico): nelle domande aperte sono tollerati
piccoli refusi (vedi _matches); a parità di punti vince chi ha meno secondi totali sulle risposte giuste.
"""
import hmac
import json
import os
import random
import re
import secrets
import threading
import time
import unicodedata
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

HOST_KEY = os.environ.get("HOST_KEY", "")
MAX_BODY = 2000
MAX_MESSAGES = 50000
MAX_POINTS, MIN_POINTS, DEFAULT_TIME = 1000, 500, 60
WAIT = 25
PODIUM = 3
# un'emoji diversa per giocatore: solo emoji a colori ovunque (niente varianti, sequenze o quasi doppioni come 🐶/🐕)
# né maiale, banana e coppa (si confonderebbe col podio)
EMOJI = list(
    "🐶🐱🐭🐹🐰🦊🐻🐼🐨🐯🦁🐮🐸🐵🐔🐧🐦🐤🦆🦅🦉🦇🐺🐗🐴🦄🐝🐛🦋🐌🐞🐜🐢🦎🦖🦕🐙🦑"
    "🦐🦞🦀🐡🐠🐟🐬🐳🦈🐊🐆🦓🦍🐘🦛🦏🐪🦒🦘🐑🦙🐐🦌🦃🦚🦜🦢🦩🦝🦡🦦🦥🦔"
    "🍎🍐🍊🍋🍉🍇🍓🍈🍒🥭🍍🥥🥝🍅🥑🥦🥒🌽🥕🧄🧅🥔🥐🍞🥨🧀🥚🍳🥞🥓🍔🍟🍕🌭🥪🌮🌯🥗🍝"
    "🍣🍙🥟🍦🍩🍪🎂🧁🥧🍫🍬🍭🍯🥤"
    "⚽🏀🏈⚾🎾🏐🎱🏓🏸🥊🎯🎳🎮🎲🧩🎸🎺🎷🥁🎻🎹🎤🎧🚀🛸🚁⛵🚲🛴🎈🎁🔮💎🔑🧲💡🔦📷🎩👑🧢⛄🌵🌲🌴🍀🍄🌻🌹🌈⭐🌙🔥🌊")
# su Render il Secret File sta in /etc/secrets, in locale si usa quiz.json accanto al server (ignorato da git)
QUIZ_PATHS = ["/etc/secrets/quiz.json", os.path.join(os.path.dirname(os.path.abspath(__file__)), "quiz.json")]


def _load_quiz():
    for path in QUIZ_PATHS:
        if os.path.exists(path):
            with open(path, encoding="utf-8") as f:
                return json.load(f)
    print("ATTENZIONE: quiz.json non trovato", flush=True)
    return []


def _normalize(text):
    text = unicodedata.normalize("NFD", str(text).lower())
    text = "".join(c for c in text if not unicodedata.combining(c))
    return re.sub(r"[^a-z0-9]+", " ", text).strip()


def _distance(a, b):
    """Distanza di Levenshtein (lettere inserite, tolte o cambiate)."""
    row = list(range(len(b) + 1))
    for i, char_a in enumerate(a, 1):
        prev, row[0] = row[0], i
        for j, char_b in enumerate(b, 1):
            prev, row[j] = row[j], min(row[j] + 1, row[j - 1] + 1, prev + (char_a != char_b))
    return row[-1]


def _matches(answer, accepted, open_question):
    """Uguali dopo la normalizzazione; nelle domande aperte basta 1 errore ogni 8 lettere (es. 'pesce' per 'pesci')."""
    answer, accepted = _normalize(answer), _normalize(accepted)
    if answer == accepted:
        return True
    return open_question and len(accepted) >= 8 and _distance(answer, accepted) <= len(accepted) // 8


def _time_limit(n):
    """Secondi a disposizione per la domanda n."""
    question = _game["quiz"][n - 1] if 0 < n <= len(_game["quiz"]) else {}
    return float(question.get("tempo", DEFAULT_TIME))


def _score(n, answer, seconds):
    """(corretta, punti) della risposta alla domanda n arrivata dopo `seconds`."""
    if not 0 < n <= len(_game["quiz"]):
        return False, 0
    question = _game["quiz"][n - 1]
    open_question = not question.get("opzioni")
    if not any(_matches(answer, accepted, open_question) for accepted in question["risposte"]):
        return False, 0
    ratio = min(seconds / _time_limit(n), 1)
    return True, round(MAX_POINTS - (MAX_POINTS - MIN_POINTS) * ratio)


def _new_game():
    # n = domanda in corso, start = ora del via, answered = (domanda, id) già risposti, emoji = id -> emoji,
    # owners = emoji -> id, scores = id -> {nome, emoji, punti, giuste, secondi}, solved = domande con già una risposta giusta
    return {"epoch": secrets.token_hex(4), "messages": [], "n": 0, "start": None, "answered": set(),
            "emoji": {}, "owners": {}, "scores": {}, "solved": set(), "quiz": _load_quiz()}


def _ranking():
    return sorted(_game["scores"].items(), key=lambda item: (-item[1]["punti"], item[1]["secondi"]))


BOOT = secrets.token_hex(4)  # cambia solo quando il processo riparte
_game = _new_game()
_lock = threading.Lock()
_changed = threading.Condition(_lock)  # svegliata a ogni via o reset, per /attesa


def _current():
    n = _game["n"]
    question = _game["quiz"][n - 1] if 0 < n <= len(_game["quiz"]) else {}
    options = question.get("opzioni", [])
    left = max(0.0, round(_time_limit(n) - (time.time() - _game["start"]), 1)) if n and _game["start"] else None
    current = {"n": n, "round": question.get("round"), "manche": question.get("manche"), "scelte": len(options),
               "opzioni": options, "restanti": left}
    if left == 0 and question.get("risposte"):
        current["soluzione"] = _solution(question)
    return current


def _solution(question):
    """Risposta giusta da mostrare a tempo scaduto: il testo dell'opzione, o la prima risposta accettata."""
    answer = str(question["risposte"][0])
    options = question.get("opzioni", [])
    index = ord(answer.strip().upper()[:1] or "?") - 65
    return options[index] if options and len(answer.strip()) == 1 and 0 <= index < len(options) else answer


def _is_host(key):
    return bool(HOST_KEY) and hmac.compare_digest(str(key), HOST_KEY)


def _emoji(player_id, wanted):
    """Emoji del giocatore: quella già sua, altrimenti quella che aveva prima di un reset/riavvio se libera, altrimenti
    una a caso tra le libere; None se sono finite."""
    if player_id in _game["emoji"]:
        return _game["emoji"][player_id]
    free = [emoji for emoji in EMOJI if emoji not in _game["owners"]]
    if not free:
        return None
    emoji = wanted if wanted in free else random.choice(free)
    _game["emoji"][player_id], _game["owners"][emoji] = emoji, player_id
    return emoji


def _append(payload, now=None):
    if len(_game["messages"]) >= MAX_MESSAGES:
        return None
    seq = len(_game["messages"]) + 1
    _game["messages"].append({"seq": seq, "time": now or time.time(), "message": json.dumps(payload)})
    return seq


class Handler(BaseHTTPRequestHandler):
    def _send(self, code, body=None):
        data = json.dumps(body if body is not None else {}).encode()
        self.send_response(code)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_OPTIONS(self):
        self._send(204)

    # input malformato (numeri non numeri ecc.): 400 con gli header CORS invece di una connessione chiusa
    def do_GET(self):
        self._safe(self._get)

    def do_POST(self):
        self._safe(self._post)

    def _safe(self, handler):
        try:
            handler()
        except (ValueError, TypeError, KeyError):
            self._send(400)

    def _get(self):
        url = urlparse(self.path)
        if url.path == "/":
            return self._send(200, {"status": "ok"})
        query = parse_qs(url.query)
        if url.path == "/classifica":
            player_id = query.get("id", [""])[0]
            with _lock:
                ranking = [{"pos": i + 1, "emoji": score["emoji"], "nome": score["nome"], "punti": score["punti"],
                            "giuste": score["giuste"], "id": pid} for i, (pid, score) in enumerate(_ranking())]
                current = _current()
                me = next((dict(row) for row in ranking if row["id"] == player_id), None)
                last = _game["scores"].get(player_id, {}).get("ultima") or {}
                answered_now = last.get("domanda") == current["n"] and current["n"] > 0
                if me and answered_now and current["restanti"] != 0:
                    me["punti"] -= last["punti"]  # svelati solo a tempo scaduto
                if me and "soluzione" in current:
                    me["esito"] = {"risposto": answered_now, "corretta": answered_now and last["corretta"],
                                   "punti": last.get("punti", 0) if answered_now else 0}
            for row in ranking + ([me] if me else []):
                row.pop("id")
            return self._send(200, {**current, "giocatori": len(ranking), "top": ranking[:PODIUM], "me": me})
        if url.path == "/attesa":
            seen = int(query.get("n", ["0"])[0] or 0)
            with _changed:
                epoch = _game["epoch"]
                _changed.wait_for(lambda: _game["n"] != seen or _game["epoch"] != epoch, timeout=WAIT)
                return self._send(200, _current())
        if url.path not in ("/msg", "/quiz"):
            return self._send(404)
        if not _is_host(query.get("key", [""])[0]):
            return self._send(403)
        if url.path == "/quiz":
            return self._send(200, {"quiz": _game["quiz"]})
        since = int(query.get("since", ["0"])[0] or 0)
        with _lock:
            body = {"epoch": _game["epoch"], "boot": BOOT, "messages": _game["messages"][since:], "restanti": _current()["restanti"]}
        self._send(200, body)

    def _post(self):
        path = urlparse(self.path).path
        length = int(self.headers.get("Content-Length", 0))
        if not 0 < length <= MAX_BODY:
            return self._send(400)
        try:
            payload = json.loads(self.rfile.read(length).decode("utf-8", "replace"))
        except ValueError:
            return self._send(400)
        if not isinstance(payload, dict):
            return self._send(400)
        with _lock:
            if path == "/msg":
                raw_answer, raw_domanda = payload.get("answer", ""), payload.get("domanda")
                player_id, name = str(payload.get("id", ""))[:40], " ".join(str(payload.get("name", "")).split())[:24]
                if payload.get("type") not in ("join", "answer") or not player_id or not name:
                    return self._send(400)
                emoji = _emoji(player_id, str(payload.get("emoji", "")))
                if not emoji:
                    return self._send(409, {"error": "full"})
                n, now = _game["n"], time.time()
                score = _game["scores"].setdefault(player_id, {"punti": 0, "giuste": 0, "secondi": 0.0})
                score.update(nome=name, emoji=emoji)
                payload = {"type": payload["type"], "id": player_id, "name": name, "emoji": emoji}
                if payload["type"] == "answer":
                    if not n:
                        return self._send(409, {"error": "not_started"})
                    if raw_domanda and raw_domanda != n:
                        # il telefono rispondeva a una domanda già superata dal via successivo
                        return self._send(409, {"error": "stale", "domanda": n})
                    if (n, player_id) in _game["answered"]:
                        return self._send(409, {"error": "already_answered", "domanda": n})
                    seconds = round(now - (_game["start"] or now), 3)
                    if seconds > _time_limit(n):
                        return self._send(409, {"error": "timeout", "domanda": n})
                    _game["answered"].add((n, player_id))
                    answer = str(raw_answer)[:200]
                    correct, points = _score(n, answer, seconds)
                    first = correct and n not in _game["solved"]
                    if correct:
                        _game["solved"].add(n)
                        score.update(punti=score["punti"] + points, giuste=score["giuste"] + 1,
                                     secondi=round(score["secondi"] + seconds, 3))
                    score["ultima"] = {"domanda": n, "corretta": correct, "punti": points}
                    payload.update(answer=answer, domanda=n, corretta=correct, secondi=seconds, punti=points, primo=first)
                seq = _append(payload, now)
                return self._send(200, {"seq": seq, "domanda": n, "emoji": emoji}) if seq else self._send(429)
            if path not in ("/login", "/question", "/reset"):
                return self._send(404)
            if not _is_host(payload.get("key", "")):
                return self._send(403, {"error": "chiave errata" if HOST_KEY else "HOST_KEY non impostata sul server"})
            if path == "/question":
                # il conduttore manda il numero, così resta allineato anche dopo un riavvio del server
                _game["n"] = int(payload.get("n") or _game["n"] + 1)
                _game["start"] = time.time()
                _append({"type": "question", "domanda": _game["n"]}, _game["start"])
                _changed.notify_all()
            elif path == "/reset":
                _game.update(_new_game())
                _changed.notify_all()
            self._send(200, {"epoch": _game["epoch"]})

    def log_message(self, *args):
        pass


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8000))
    print(f"skydo server su :{port}" + ("" if HOST_KEY else " (ATTENZIONE: HOST_KEY non impostata)"), flush=True)
    server = ThreadingHTTPServer(("0.0.0.0", port), Handler)
    server.daemon_threads = True
    server.serve_forever()
