"""Collect an explicit Lean import closure without copying compiled artifacts."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
from pathlib import Path


def uncomment(text: str) -> str:
    out = []
    depth = 0
    quoted = False
    i = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == "\\" and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
                continue
            if text[i] == '"':
                quoted = False
            i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.append(" ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            quoted = text[i] == '"'
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unclosed Lean comment")
    return "".join(out)


def imports(text: str) -> list[str]:
    result = []
    for line in uncomment(text).splitlines():
        m = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.*?)\s*$", line)
        if not m:
            continue
        for name in m[1].split():
            if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", name):
                raise ValueError(f"Unsupported import syntax: {line}")
            result.append(name)
    return result


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("source", type=Path)
    p.add_argument("destination", type=Path)
    p.add_argument("--ledger", type=Path)
    p.add_argument("--fallback", type=Path, action="append", default=[])
    p.add_argument("--root", action="append", default=[])
    args = p.parse_args()
    roots = list(args.root)
    if args.ledger:
        roots += sorted({e["module"] for e in json.loads(args.ledger.read_text())["entries"].values()
                         if e.get("module")})
    done = set()
    visiting = set()
    records = []
    source = args.source.resolve()
    dest = args.destination.resolve()
    external = {"Mathlib", "Lean", "Init", "Std", "Batteries", "Aesop", "Qq", "Plausible"}

    def visit(name: str) -> None:
        if name.split(".")[0] in external or name in done:
            return
        if name in visiting:
            raise ValueError(f"Import cycle at {name}")
        rel = Path(*name.split(".")).with_suffix(".lean")
        candidates = [root / rel for root in [source, *args.fallback]]
        path = next((p for p in candidates if p.is_file() and p.stat().st_size), None)
        if path is None:
            raise ValueError(f"Missing or empty source for {name}: {candidates}")
        text = path.read_text()
        clean = uncomment(text)
        if re.search(r"\b(sorry|admit|sorryAx|native_decide)\b|^\s*axiom\b", clean, re.M):
            raise ValueError(f"Unfinished or policy-rejected proof source: {name}")
        visiting.add(name)
        for dep in imports(text):
            visit(dep)
        visiting.remove(name)
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists() and target.read_bytes() != path.read_bytes():
            raise ValueError(f"Refusing to overwrite edited source: {target}")
        if path.resolve() != target.resolve():
            shutil.copyfile(path, target)
        records.append({"module": name, "source": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
        done.add(name)

    for root in roots:
        visit(root)
    local = dest / ".local"
    local.mkdir(exist_ok=True)
    manifest = local / "imported-sources.json"
    previous = json.loads(manifest.read_text()) if manifest.exists() else []
    combined = {r["module"]: r for r in previous + records}
    manifest.write_text(json.dumps(list(combined.values()), indent=2) + "\n")
    (local / "roots.json").write_text(json.dumps(roots, indent=2) + "\n")
    config = '''name = "QiushiMatmulProof"
version = "0.1.0"
defaultTargets = ["QiushiMatmul"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "0df444a360eaa60ab8c11dca51a86af692955474"

[[lean_lib]]
name = "QiushiMatmul"
'''
    all_modules = sorted(".".join(p.relative_to(dest).with_suffix("").parts)
                         for p in dest.rglob("*.lean")
                         if not any(part.startswith(".") for part in p.relative_to(dest).parts))
    config += "roots = " + json.dumps(all_modules) + "\n"
    config += "globs = " + json.dumps(all_modules) + "\n"
    (dest / "lakefile.toml").write_text(config)
    print(json.dumps({"source_modules": len(done), "source_bytes": sum((dest / Path(*m.split('.')).with_suffix('.lean')).stat().st_size for m in done), "roots": len(roots)}))


if __name__ == "__main__":
    main()
