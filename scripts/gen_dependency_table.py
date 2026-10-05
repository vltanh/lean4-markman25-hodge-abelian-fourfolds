#!/usr/bin/env python3
"""Turn the table that `lake env lean scripts/Audit.lean` prints into Section 8 of REPORT.md.

usage: lake env lean scripts/Audit.lean > audit.out; python3 scripts/gen_dependency_table.py audit.out
Prints a Markdown table: result, Lean declaration, results from prior work used (axioms omitted: the
audit checks that they are the standard ones)."""
import re, sys
rows = []
for line in open(sys.argv[1]):
    m = re.match(r'\| (.+?) \| `([^`]+)` \| (.+?) \| (.+?) \|\s*$', line.rstrip('\n'))
    if not m or m.group(1) == 'Result':
        continue
    label, name, uses, axs = m.groups()
    short = name.replace('WeilClasses.', '')
    uses = ', '.join('`' + u.strip('` ').replace('WeilClasses.', '') + '`' for u in uses.split(',')) if uses.strip() != '–' else '–'
    rows.append(f'| {label} | `{short}` | {uses} |')
print('| Result | Lean | Results from prior work used |')
print('|---|---|---|')
print('\n'.join(rows))
