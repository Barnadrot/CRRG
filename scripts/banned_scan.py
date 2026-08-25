#!/usr/bin/env python3
"""Banned-construct scan for CRRG (Spec 14.2 item 2, 5.6, 14.2 item 7).

The axiom audit catches holes that reach the kernel. This catches the ones that
do not: escape hatches that keep a declaration axiom-clean while defeating the
trust model, and any attempt to emit an aggregate progress magnitude.

Lean comments are stripped before matching, so a doc-comment may quote the spec
(and name a banned construct) without tripping the scan. Nested block comments
are handled, since Lean's `/- -/` nests.
"""
import re, sys, pathlib

# Kernel escape hatches: admitted holes, compiler trust, new assumptions,
# runtime replacement of a verified definition, opting out of termination.
CONSTRUCTS = [
    (re.compile(r'(?<![A-Za-z_])sorry(?![A-Za-z_])'), "sorry (admitted hole)"),
    (re.compile(r'(?<![A-Za-z_])native_decide(?![A-Za-z_])'), "native_decide (trusts the compiler, not the kernel)"),
    (re.compile(r'^\s*axiom\s'), "axiom (new trusted assumption)"),
    (re.compile(r'^\s*unsafe\s'), "unsafe"),
    (re.compile(r'^\s*partial\s'), "partial (opts out of termination checking)"),
    (re.compile(r'@\[\s*(implemented_by|extern)'), "@[implemented_by]/@[extern] (replaces the verified definition)"),
]

# Spec 5.6 / 14.2 item 7: no synthetic global percentage, no aggregate count.
AGGREGATES = [
    (re.compile(r'(?i)percentage|percentSolved|progressScore|completionRatio'
                r'|fractionSolved|overallProgress|globalScore'), "aggregate progress magnitude"),
]

def strip_comments(src: str) -> str:
    """Replace Lean comments with spaces, preserving line structure."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith('--', i):
            j = src.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j
        elif src.startswith('/-', i):
            depth += 1; out.append('  '); i += 2
        elif depth > 0 and src.startswith('-/', i):
            depth -= 1; out.append('  '); i += 2
        elif depth > 0:
            out.append('\n' if src[i] == '\n' else ' '); i += 1
        else:
            out.append(src[i]); i += 1
    return ''.join(out)

def main(argv):
    targets = argv[1:] or ["CRRG"]
    failed = False
    print("=== CRRG banned-construct scan ===")
    for t in targets:
        root = pathlib.Path(t)
        files = sorted(root.rglob("*.lean")) if root.is_dir() else [root]
        print(f"Scanning: {t} ({len(files)} files)")
        for f in files:
            code = strip_comments(f.read_text(encoding="utf-8"))
            for lineno, line in enumerate(code.split("\n"), 1):
                for rx, why in CONSTRUCTS + AGGREGATES:
                    if rx.search(line):
                        print(f"  BANNED: {f}:{lineno}: {why}")
                        print(f"    {line.strip()[:100]}")
                        failed = True
    if failed:
        print("\n=== BANNED-CONSTRUCT SCAN FAILED ===")
        print("A construct above defeats the trust model or emits an aggregate magnitude.")
        return 1
    print("  no banned constructs, no aggregate magnitudes")
    print("=== Banned-construct scan PASSED ===")
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv))
