"""Local dialogue experiment. Never emits or writes a production Lean receipt.

The original Forge evaluator and search are imported, not reimplemented.
Chat adaptation is new and deliberately has no pretrained language model.
"""
import copy
import hashlib
import json
import os
from pathlib import Path
from tools.autonomy import forge_lean_evolution as evo

CAP = 128
WIDTH = 16
STATUS = "FINITE_CHECKED_NOT_LEAN_VERIFIED"

def need(ok, msg):
    if not ok:
        raise ValueError(msg)

def sha(v):
    return hashlib.sha256(bytes(v)).hexdigest()

def canonical(v):
    return json.dumps(v, ensure_ascii=False, sort_keys=True, separators=(",", ":"))

def project(text):
    data = text.encode("utf-8")
    out = [0] * WIDTH
    for i, b in enumerate(data):
        j = i % WIDTH
        out[j] = ((out[j] * 33) ^ b ^ ((i // WIDTH) & 255)) & 255
    out[-1] ^= len(data) & 255
    return out

def check_table(v):
    need(isinstance(v, list) and len(v) == 256 and
         all(type(x) is int and 0 <= x < 256 for x in v), "invalid table")

def finite_table(recipe, tables):
    if recipe[0] == "production":
        spec = recipe[1:]
        v = evo.evaluate(spec, tables)
        need(v == evo.evaluate(spec, tables, independent=True), "interpreter mismatch")
        need(all(v[v[x]] == x for x in range(256)), "involution mismatch")
    elif recipe[0] == "composition":
        need(len(recipe) == 3, "invalid composition")
        a, b = (tables[k] for k in recipe[1:])
        v = [b[a[x]] for x in range(256)]
        independent = []
        for x in range(256):
            intermediate = a[x]
            independent.append(next(y for j, y in enumerate(b) if j == intermediate))
        need(v == independent, "composition mismatch")
    else:
        raise ValueError("unknown recipe")
    check_table(v)
    return v

class Engine:
    def __init__(self, path, snapshot_text):
        self.path = Path(path)
        self.snapshot = json.loads(snapshot_text)
        need(self.snapshot["schema"] == 1 and
             self.snapshot["verification"] == "ORIGINAL_LEAN_REPLAY", "invalid snapshot")
        self.snapshot_hash = hashlib.sha256(snapshot_text.encode("utf-8")).hexdigest()
        self.roots = {}
        for key, table, digest in self.snapshot["tables"]:
            check_table(table)
            need(key not in self.roots and sha(table) == digest, "snapshot table mismatch")
            self.roots[key] = table
        need(bool(self.roots), "no seed operators")
        if self.path.exists():
            self.state = json.loads(self.path.read_text(encoding="utf-8"))
            need(self.state["schema"] == 1 and self.state["snapshot_sha256"] == self.snapshot_hash,
                 "saved state belongs to a different snapshot; keep the old state for export")
        else:
            self.state = {"schema": 1, "snapshot_sha256": self.snapshot_hash, "turns": [],
                          "locals": [], "scores": {}, "latent": list(range(WIDTH)),
                          "alphabet": [], "pending": None, "last_search": None}
        self.tables = dict(self.roots)
        need(len(self.state["locals"]) <= CAP, "local limit exceeded")
        for row in self.state["locals"]:
            v = finite_table(row["recipe"], self.tables)
            digest = sha(v)
            key = "local:" + digest
            need(row["status"] == STATUS and row["id"] == key and
                 row["behavior_sha256"] == digest and key not in self.tables and
                 v not in self.tables.values(), "local receipt drift")
            self.tables[key] = v
        self.save()

    def save(self):
        self.path.parent.mkdir(parents=True, exist_ok=True)
        tmp = self.path.with_suffix(".tmp")
        with tmp.open("w", encoding="utf-8") as f:
            f.write(canonical(self.state))
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, self.path)

    def transact(self, fn):
        previous, tables = copy.deepcopy(self.state), dict(self.tables)
        try:
            out = fn()
            self.save()
            return out
        except BaseException:
            self.state, self.tables = previous, tables
            raise

    def admit(self, recipe, origin):
        if len(self.state["locals"]) >= CAP:
            return None
        v = finite_table(recipe, self.tables)
        if v in self.tables.values():
            return None
        digest = sha(v)
        key = "local:" + digest
        self.state["locals"].append({"id": key, "recipe": recipe,
            "behavior_sha256": digest, "status": STATUS, "origin": origin})
        self.tables[key] = v
        return key

    def _send(self, text):
        # A computational turn is deliberately not a language-model training target.
        if text.strip() == "演算子の偶奇観測商":
            from forge_finite import quotient, distinguish
            keys = list(self.tables)
            actions = [self.tables[key] for key in keys]
            obs = [x % 2 for x in range(256)]
            r = quotient(actions, obs)
            c = r["class_of"]
            pair = next(((x, y) for x in range(256) for y in range(x)
                         if obs[x] == obs[y] and c[x] != c[y]), None)
            response = f"安定商 {len(r['classes'])} 状態、細分化 {r['rounds']} 回。"
            if pair:
                w = distinguish(actions, obs, *pair)
                response += f" 初期観測が等しい {pair} の最短識別列（1始まり）: " + str([a + 1 for a in w["word"]])
            self.state["pending"] = None
            self.state["turns"].append({
                "turn": len(self.state["turns"]) + 1, "input": text,
                "output": response, "operator": "FINITE_CHECKED_NOT_LEAN_VERIFIED",
                "new": [], "raw_hex": "", "feedback": "NO_TRAINING_ON_COMPUTATION"})
            return self.view()

        need(isinstance(text, str) and 0 < len(text) <= 4096, "input must be 1–4096 characters")
        s = self.state
        target = project(text)
        turn = len(s["turns"])
        # Next utterance is feedback, not a judgment of semantic correctness.
        if s["pending"] is not None:
            probe = s["pending"]["probe"]
            for key in s["pending"]["operators"]:
                prediction = [self.tables[key][x] for x in probe]
                loss = sum((a ^ b).bit_count() for a, b in zip(prediction, target))
                old = s["scores"].get(key, 0)
                s["scores"][key] = (old * 7 + (64 - loss) * 8) // 8
        for ch in text:
            if ch.isprintable() and not ch.isspace() and ch not in s["alphabet"] and len(s["alphabet"]) < 256:
                s["alphabet"].append(ch)
        # Both learned scores and the input affect future operator selection.
        probe = [a ^ b for a, b in zip(s["latent"], target)]
        d = hashlib.sha256(bytes(probe) + text.encode("utf-8")).digest()
        keys = list(self.tables)
        ranked = sorted(keys, key=lambda k: (-s["scores"].get(k, 0), k))
        parent = ranked[d[0] % min(len(ranked), 4)] if turn % 4 else keys[d[0] % len(keys)]
        t = d[1] % 8
        others = [-1] + [i for i in range(8) if i != t]
        recipe = ["production", parent, t, d[2] % 8, others[d[3] % 8], ("and", "xor")[d[4] % 2]]
        new = []
        key = self.admit(recipe, "dialogue")
        if key:
            new.append(key)
        key = self.admit(["composition", parent, list(self.tables)[d[5] % len(self.tables)]], "dialogue")
        if key:
            new.append(key)
        keys = list(self.tables)
        # Deterministic exploration includes newly generated operators.
        chosen = new[-1] if new and turn % 4 == 0 else (
            keys[d[6] % len(keys)] if turn % 4 == 1 else
            max(keys, key=lambda k: (s["scores"].get(k, 0), k)))
        result = [self.tables[chosen][x] for x in probe]
        alphabet = s["alphabet"]
        output = "".join(alphabet[b % len(alphabet)] for b in result) if alphabet else bytes(result).hex()
        s["latent"] = result
        s["pending"] = {"probe": probe, "operators": keys}
        row = {"turn": turn + 1, "input": text, "output": output, "operator": chosen,
               "new": new, "raw_hex": bytes(result).hex(), "feedback": "NEXT_INPUT_BIT_DISTANCE"}
        s["turns"].append(row)
        return self.view()

    def send(self, text):
        return self.transact(lambda: self._send(text))

    def _search(self):
        if len(self.state["locals"]) >= CAP:
            self.state["last_search"] = {"status": "LOCAL_LIMIT", "limit": CAP}
            return self.view()
        # Same exact bounded search, but over the local experimental alphabet.
        # No proof or production-ledger promotion is attempted.
        chosen, invariants, counts = evo.search(self.tables)
        report = {"status": "NO_CANDIDATE", "search": counts, "invariants": invariants}
        if chosen is not None:
            recipe, v, inv, pair = chosen
            need(finite_table(["production"] + list(recipe), self.tables) == v, "search replay mismatch")
            key = self.admit(["production"] + list(recipe), "original_forge_search")
            need(key is not None, "search selected duplicate")
            report.update({"status": STATUS, "operator": key, "invariant": inv, "witness": pair})
        self.state["last_search"] = report
        return self.view()

    def search(self):
        return self.transact(self._search)

    def view(self):
        return {"certified": self.snapshot["generation_count"], "roots": len(self.roots),
                "local": len(self.state["locals"]), "limit": CAP,
                "turn_count": len(self.state["turns"]), "alphabet_size": len(self.state["alphabet"]),
                "turns": self.state["turns"][-100:], "last_search": self.state["last_search"]}

    def export(self):
        return canonical({"schema": 1, "snapshot": self.snapshot, "experiment": self.state})

_engine = None

def start(path, snapshot):
    global _engine
    _engine = Engine(path, snapshot)
    return canonical(_engine.view())

def send(text):
    return canonical(_engine.send(text))

def search():
    return canonical(_engine.search())

def export_state():
    return _engine.export()
