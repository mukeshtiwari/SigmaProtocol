#!/usr/bin/env python3
"""usage: run_deep.py SCRIPT.py ARGS...

Run a Python script with a large recursion limit and stack: the λ□ terms of
the extracted programs are deeper than Python's default limit allows."""
import os, runpy, sys, threading

def run():
    try:
        runpy.run_path(script, run_name='__main__')
    except SystemExit as e:
        code = e.code
        if isinstance(code, str):
            print(code, file=sys.stderr)
            code = 1
        sys.stdout.flush()
        os._exit(code or 0)
    except BaseException:
        import traceback
        traceback.print_exc()
        sys.stdout.flush()
        os._exit(1)
    sys.stdout.flush()
    os._exit(0)

script = sys.argv[1]
sys.argv = sys.argv[1:]
sys.path.insert(0, os.path.dirname(os.path.abspath(script)))
sys.setrecursionlimit(1000000)
threading.stack_size(1 << 30)
threading.Thread(target=run).start()
