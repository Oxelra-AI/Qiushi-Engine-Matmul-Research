"""Build a collected source closure with Lake and bounded process concurrency."""
import argparse
import concurrent.futures
import contextlib
import fcntl
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
import tomllib

from source_graph import imports
from lean_resources import configure_process_stack

p = argparse.ArgumentParser()
p.add_argument("project", type=Path)
p.add_argument("--jobs", type=int, default=4)
p.add_argument("--batch-size", type=int, default=1)
p.add_argument("--lake", default="lake")
selection = p.add_mutually_exclusive_group()
selection.add_argument("--root", action="append")
selection.add_argument("--all", action="store_true",
                       help="build every concrete lean_lib root registered in lakefile.toml")
p.add_argument("--resume-from", type=Path,
               help="revalidate successful previous targets with Lake before resuming")
p.add_argument("--fresh-lean", action="store_true",
               help="compile a source snapshot directly with Lean into isolated outputs")
args = p.parse_args()
if args.jobs < 1:
    p.error("--jobs must be positive")
if args.batch_size < 1 or args.batch_size > args.jobs:
    p.error("--batch-size must be between 1 and --jobs")
project = args.project.resolve()
roots = args.root or ["QiushiMatmul"]
if args.all:
    try:
        with (project / "lakefile.toml").open("rb") as config_file:
            config = tomllib.load(config_file)
    except (OSError, ValueError) as error:
        p.error(f"Cannot read lakefile.toml registrations: {error}")
    libraries = config.get("lean_lib")
    if not isinstance(libraries, list) or not libraries:
        p.error("--all requires nonempty [[lean_lib]] registrations in lakefile.toml")
    roots = []
    for index, library in enumerate(libraries):
        registered = library.get("roots") if isinstance(library, dict) else None
        if not isinstance(registered, list) or not registered:
            p.error(f"lean_lib[{index}].roots must be a nonempty list of concrete module names")
        roots.extend(registered)
for root in roots:
    if not isinstance(root, str) or any(
            not part.strip() or "/" in part or "\\" in part for part in root.split(".")):
        p.error(f"Invalid concrete root module name: {root!r}")
    path = project / Path(*root.split(".")).with_suffix(".lean")
    if not path.is_file():
        p.error(f"Root module does not exist: {root}")
roots = list(dict.fromkeys(roots))
try:
    process_stack = configure_process_stack()
except RuntimeError as error:
    p.error(str(error))
graph = {}

def visit(name):
    path = project / Path(*name.split(".")).with_suffix(".lean")
    if name in graph or not path.is_file():
        return
    deps = [d for d in imports(path.read_text())
            if (project / Path(*d.split(".")).with_suffix(".lean")).is_file()]
    graph[name] = deps
    for dep in deps:
        visit(dep)

for root in roots:
    visit(root)
priority = dict.fromkeys(graph, 0)
todo = [(root, 0) for root in roots]
while todo:
    name, depth = todo.pop()
    if depth < priority[name]:
        continue
    if depth > len(graph):
        raise RuntimeError("Import cycle")
    priority[name] = depth
    todo.extend((dep, depth + 1) for dep in graph[name]
                if depth + 1 > priority[dep])
out = project / ".local" / ("build-" + time.strftime("%Y%m%d-%H%M%S"))
out.mkdir(parents=True)

def publish_json(name, value):
    temporary = out / (name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(out / name)

publish_json("process-stack.json", process_stack)

locks = project / '.local' / 'module-locks'
locks.mkdir(exist_ok=True)
manifest = json.loads((project / "lake-manifest.json").read_text())
print(f"Building {len(graph)} modules; logs {out}", flush=True)
fresh_env = None
if args.fresh_lean:
    if args.batch_size != 1:
        p.error("--fresh-lean requires --batch-size 1")
    probe = subprocess.run([args.lake, "env", "python3", "-c",
        "import json,os,shutil; print(json.dumps({'path':os.environ['LEAN_PATH'],"
        "'lean':shutil.which('lean')}))"], cwd=project, check=True,
        text=True, stdout=subprocess.PIPE)
    config = json.loads(probe.stdout)
    lean = config["lean"]
    if not lean or not Path(lean).is_file():
        raise RuntimeError("Lake did not resolve its Lean compiler")
    libraries = []
    for item in config["path"].split(os.pathsep):
        path = Path(item)
        path = (project / path).resolve() if not path.is_absolute() else path.resolve()
        if path.is_relative_to((project / ".lake/packages").resolve()):
            libraries.append(str(path))
    if not libraries:
        raise RuntimeError("No pinned package libraries found in Lake's environment")
    source_dir = out / "src"
    object_dir = out / "lib"
    source_dir.mkdir()
    object_dir.mkdir()
    for name in graph:
        relative = Path(*name.split(".")).with_suffix(".lean")
        target = source_dir / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(project / relative, target)
    fresh_env = dict(os.environ,
                     LEAN_PATH=os.pathsep.join([str(object_dir)] + libraries))
    (out / "environment.json").write_text(json.dumps({
        "lean": lean, "lean_path": fresh_env["LEAN_PATH"],
        "source_snapshot": str(source_dir), "objects": str(object_dir),
        "manifest": manifest, "process_stack": process_stack}, indent=2) + "\n")

def run(names):
    start = time.monotonic()
    env = fresh_env or os.environ.copy()
    if fresh_env is None:
        cmd = [args.lake, "--no-cache", "build"] + ["+" + n + ":olean" for n in names]
        cwd = project
    else:
        relative = Path(*names[0].split(".")).with_suffix(".lean")
        artifact = (object_dir / relative).with_suffix(".olean")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        # Match Lake's stack setting for the complete calibration-table proof.
        # The pinned Lean ignores LEAN_NUM_THREADS; bound its worker pool via CLI.
        cmd = [lean, "--threads=1", "-s262144", "-R", str(source_dir), "-o", str(artifact),
               str(source_dir / relative)]
        cwd = source_dir
    log_path = out / (names[0] + ".log")
    with contextlib.ExitStack() as stack:
        for name in sorted(names) if fresh_env is None else []:
            lock = stack.enter_context((locks / (name + '.lock')).open('a'))
            fcntl.flock(lock, fcntl.LOCK_EX)
        log = stack.enter_context(log_path.open("w"))
        result = subprocess.run(cmd, cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT)
        if fresh_env is not None and result.returncode == 0 and not artifact.is_file():
            raise RuntimeError(f"Lean returned success without producing {artifact}")
    # A failed batch never certifies any member as successful.
    return [{"module": name, "returncode": result.returncode,
             "seconds": round(time.monotonic() - start, 2), "log": log_path.name,
             "batch": names} for name in names]

pending = set(graph)
done = {}
if args.resume_from:
    if args.fresh_lean:
        p.error("a fresh build cannot reuse prior project outputs")
    records = json.loads(args.resume_from.read_text())
    candidates = sorted({record['module'] for record in records
                         if record['returncode'] == 0 and record['module'] in graph})
    if candidates:
        command = [args.lake, '--no-cache', '--no-build', 'build'] + [
            '+' + name + ':olean' for name in candidates]
        with (out / 'resume-cache-check.log').open('w') as log:
            check = subprocess.run(command, cwd=project, stdout=log,
                                   stderr=subprocess.STDOUT)
        if check.returncode == 0:
            for name in candidates:
                done[name] = {'module': name, 'returncode': 0,
                              'cache_revalidated': True, 'log': 'resume-cache-check.log'}
                pending.remove(name)
            print(f'Revalidated {len(candidates)} cached modules with Lake', flush=True)
        else:
            print('Cache revalidation failed; rebuilding through normal scheduling', flush=True)
active = {}
with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
    while pending or active:
        blocked = [n for n in pending if any(d in done and done[d]["returncode"] for d in graph[n])]
        for name in blocked:
            done[name] = {"module": name, "returncode": 125, "blocked_by":
                          [d for d in graph[name] if d in done and done[d]["returncode"]]}
            pending.remove(name)
        ready = sorted((n for n in pending
                        if all(d in done and done[d]["returncode"] == 0 for d in graph[n])),
                       key=lambda n: (-priority[n], n))
        available = max(0, args.jobs - sum(len(batch) for batch in active.values()))
        admitted = ready[:available]
        for start in range(0, len(admitted), args.batch_size):
            batch = admitted[start:start + args.batch_size]
            active[pool.submit(run, batch)] = batch
            pending.difference_update(batch)
        if not active:
            if blocked:
                continue
            if pending:
                raise RuntimeError(f"Import cycle: {sorted(pending)}")
            break
        completed, _ = concurrent.futures.wait(active, return_when=concurrent.futures.FIRST_COMPLETED)
        for task in completed:
            records = task.result()
            active.pop(task)
            for record in records:
                done[record['module']] = record
                print(json.dumps(record), flush=True)
        publish_json("results.json", list(done.values()))
publish_json("results.json", list(done.values()))
summary = {"modules": len(graph), "ok": sum(x["returncode"] == 0 for x in done.values()),
           "failed": [n for n, x in done.items() if x["returncode"] not in (0, 125)],
           "blocked": [n for n, x in done.items() if x["returncode"] == 125]}
publish_json("summary.json", summary)
print(json.dumps(summary), flush=True)
raise SystemExit(bool(summary["failed"] or summary["blocked"]))
