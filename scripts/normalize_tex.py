#!/usr/bin/env python3
"""Normalize Markman's TeX (arXiv:2502.03415v2) for route_check.py extract.

- strips TeX comments and the bodies of \\hide{...} (the paper defines \\newcommand{\\hide}[1]{},
  so these blocks are not part of the paper);
- renames the paper's theorem environments to the names route_check.py recognizes:
  thm->theorem, lem->lemma, prop->proposition, cor->corollary, conj->conjecture.
Usage: normalize_tex.py IN.tex > OUT.tex
"""
import re, sys

def strip_comments(s):
    out = []
    for line in s.split('\n'):
        i, res = 0, ''
        while i < len(line):
            c = line[i]
            if c == '\\' and i + 1 < len(line):
                res += line[i:i+2]; i += 2; continue
            if c == '%':
                break
            res += c; i += 1
        out.append(res)
    return '\n'.join(out)

def strip_hide(s):
    res, i, n = [], 0, len(s)
    while i < n:
        j = s.find('\\hide{', i)
        if j < 0:
            res.append(s[i:]); break
        res.append(s[i:j])
        k, depth = j + len('\\hide{'), 1
        while k < n and depth > 0:
            c = s[k]
            if c == '\\':
                k += 2; continue
            if c == '{': depth += 1
            elif c == '}': depth -= 1
            k += 1
        res.append('\n' * s[j:k].count('\n'))
        i = k
    return ''.join(res)

s = strip_hide(strip_comments(open(sys.argv[1], encoding='utf-8').read()))
# keep the preamble's \newcommand{\hide}[1]{} harmless; rename environments
for a, b in [('thm', 'theorem'), ('lem', 'lemma'), ('prop', 'proposition'), ('cor', 'corollary'),
             ('conj', 'conjecture')]:
    s = re.sub(r'\\(begin|end)\{' + a + r'\}', r'\\\1{' + b + '}', s)
sys.stdout.write(s)
