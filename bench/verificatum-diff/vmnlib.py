"""The Verificatum mix-net proof format (VMN 3.1.0, "How to Implement a
Stand-alone Verifier for the Verificatum Mix-Net", Sections 4 and 7): byte
trees and the group parameters of a protocol info file, for reading and
mutating proof directories produced by vmn."""
import re, struct

# ---- byte trees (Section 4): ('leaf', bytes) | ('node', [children]) ----

def bt_decode(b, pos=0):
    tag = b[pos]; n = struct.unpack(">I", b[pos + 1:pos + 5])[0]; pos += 5
    if tag == 1:
        return ("leaf", bytes(b[pos:pos + n])), pos + n
    if tag != 0:
        raise ValueError("bad tag")
    cs = []
    for _ in range(n):
        c, pos = bt_decode(b, pos); cs.append(c)
    return ("node", cs), pos

def bt_load(path):
    data = open(path, "rb").read()
    t, pos = bt_decode(data)
    if pos != len(data): raise ValueError("trailing data")
    return t

def bt_encode(t):
    if t[0] == "leaf":
        return b"\x01" + struct.pack(">I", len(t[1])) + t[1]
    return b"\x00" + struct.pack(">I", len(t[1])) + b"".join(bt_encode(c) for c in t[1])

def bt_save(path, t):
    open(path, "wb").write(bt_encode(t))

def width_of(m):   # bytes of the fixed-size two's complement representation
    k = 1
    while m >= 1 << (8 * k - 1): k += 1
    return k

def to_bytes(k, x): return x.to_bytes(k, "big", signed=True)
def of_bytes(b): return int.from_bytes(b, "big", signed=True)

class Group:
    """p, q, g of the ModPGroup of a protocol info file."""
    def __init__(self, protinfo):
        x = open(protinfo).read()
        s_gq = re.search(r"<pgroup>(.*?)</pgroup>", x, re.S).group(1).strip()
        gt, _ = bt_decode(bytes.fromhex(s_gq.split("::")[-1]))
        cls, params = gt[1]
        assert cls[1] == b"com.verificatum.arithm.ModPGroup"
        self.p, self.q, self.g = (of_bytes(c[1]) for c in params[1][:3])
        self.kp, self.kq = width_of(self.p), width_of(self.q)
