#!/usr/bin/env python3
"""clang2elpi.py FILE.hpp [clang options..]: the C++ functions of FILE, as
parsed by clang, printed as Elpi facts `cxx-function N`, N being clang's AST
(-ast-dump=json) written as a tree of `n Kind Attrs Children` (cxx-ast in
cxxfront.elpi). Nothing is interpreted here: the translation to L0 is Elpi's
(cxxfront.elpi). Only the functions written in FILE are kept, not those of
the headers it includes."""
import json, subprocess, sys

src, opts = sys.argv[1], sys.argv[2:]
out = subprocess.run(["clang++", "-std=c++17", "-fsyntax-only", "-Xclang", "-ast-dump=json", *opts, src],
                     capture_output=True, text=True)
if out.returncode:
    sys.exit(out.stderr)


text = open(src, "rb").read()                            # clang counts bytes


def q(s):
    return '"' + str(s).replace("\\", "\\\\").replace('"', '\\"') + '"'


def attrs(node):
    a = []
    for k in ("name", "opcode", "value", "init", "isPostfix", "hasElse"):
        if k in node:
            a.append((k, node[k]))
    if node["kind"].endswith("Decl") and "id" in node:      # what a DeclRefExpr refers to
        a.append(("id", node["id"]))
    if node["kind"].endswith("Literal"):                     # the literal as written
        b = node.get("range", {}).get("begin", {})
        b = b.get("spellingLoc", b)
        if "offset" in b and "tokLen" in b:
            a.append(("text", text[b["offset"]:b["offset"] + b["tokLen"]].decode()))
    if "type" in node:
        a.append(("type", node["type"].get("qualType", "")))
    if "referencedDecl" in node:
        a.append(("ref", node["referencedDecl"]["id"]))
        a.append(("refname", node["referencedDecl"].get("name", "")))
    return a


def term(node, ind):
    kids = [k for k in node.get("inner", []) if k]
    a = ", ".join(f"a {q(k)} {q(str(v).lower() if isinstance(v, bool) else v)}" for k, v in attrs(node))
    head = f"n {q(node['kind'])} [{a}]"
    if not kids:
        return head + " []"
    sub = ",\n".join(ind + "  " + term(k, ind + "  ") for k in kids)
    return head + " [\n" + sub + "]"


# The functions of the file itself: clang marks a declaration of an included
# header with includedFrom, and writes the file name once, at its first
# declaration; a later declaration of the same file has no file name.
facts, cur = [], None
def walk(node):
    global cur
    loc = node.get("loc", {})
    loc = loc.get("expansionLoc", loc)
    if "file" in loc:
        cur = loc["file"]
    inc = "includedFrom" in loc or (cur is not None and cur != src)
    k = node.get("kind")
    if k in ("FunctionTemplateDecl", "FunctionDecl") and not inc and not node.get("isImplicit"):
        facts.append(node); return
    for c in node.get("inner", []):
        walk(c)

walk(json.loads(out.stdout))
print(f"% the functions of {src}, parsed by clang (tools/clang2elpi.py)")
for f in facts:
    print("cxx-function (" + term(f, "") + ").")
