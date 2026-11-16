"""Imports Helios's crypto code (helios/crypto/algs.py and utils.py of the
pinned helios-server submodule) unmodified. helios/__init__.py needs Django
settings, so a stub package is built in a temporary directory with empty
__init__ files and the one-line to_json of helios_auth/utils.py, and the three
crypto modules (algs.py, utils.py, electionalgs.py) are symlinked from the
submodule (as bench/verify_iacr_python.py)."""
import os, sys, tempfile

HELIOS_SERVER = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "helios-server")

def load():
    root = tempfile.mkdtemp(prefix="helios_stub_")
    os.makedirs(os.path.join(root, "helios", "crypto"))
    open(os.path.join(root, "helios", "__init__.py"), "w").close()
    open(os.path.join(root, "helios", "crypto", "__init__.py"), "w").close()
    with open(os.path.join(root, "helios", "utils.py"), "w") as f:
        f.write("import json\n\ndef to_json(d):\n    return json.dumps(d, sort_keys=True)\n")
    for mod in ("algs.py", "utils.py", "electionalgs.py"):
        os.symlink(os.path.abspath(os.path.join(HELIOS_SERVER, "helios", "crypto", mod)),
                   os.path.join(root, "helios", "crypto", mod))
    sys.path.insert(0, root)
    import helios.crypto.algs as algs
    import helios.crypto.utils as cutils
    import helios.crypto.electionalgs as ealgs
    load.electionalgs = ealgs
    return algs, cutils
