#!/usr/bin/env python3
"""Generate scripts/Audit.lean from its template scripts/Audit.lean.in and the library.

Run from anywhere: `python3 scripts/gen_audit.py` (or `--check` to verify that the file is current);
then `lake env lean scripts/Audit.lean`.

- `import all` for every module of the library (and Solution);
- externalResults: every theorem of WeilClasses/External/, every Prop-valued definition there
  (an assumed cited result) and every hypothesis class of WeilClasses/Defs.lean (the assumed
  results of the conditional formalization);
- paperResults: every declaration whose docstring starts with a bold paper number
  (`**Lemma 2.2.1**`, `**(6.1.3)**`, ...), in the order of the paper;
- solutionResults: the theorems of `namespace WeilClasses.Challenge` in Challenge.lean.
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEMPLATE = ROOT / 'scripts/Audit.lean.in'

mods = sorted(p.relative_to(ROOT).with_suffix('').as_posix().replace('/', '.')
              for p in (ROOT / 'WeilClasses').rglob('*.lean'))

DECL = re.compile(r'^(?:theorem|lemma|noncomputable def|def|class|structure|abbrev|noncomputable abbrev)\s+'
                  r'(_root_\.)?([^\s(:{\[]+)', re.M)


def decls_with_docs(text):
    """(name, docstring, namespace) for declarations with a docstring."""
    out = []
    ns_stack = []
    lines = text.split('\n')
    i = 0
    doc = None
    while i < len(lines):
        l = lines[i]
        m = re.match(r'^namespace\s+(\S+)', l)
        if m:
            ns_stack.append(m.group(1))
        m = re.match(r'^end\s+(\S+)', l)
        if m and ns_stack and ns_stack[-1] == m.group(1):
            ns_stack.pop()
        if l.startswith('/--'):
            j = i
            buf = l
            while '-/' not in lines[j]:
                j += 1
                buf += '\n' + lines[j]
            doc = buf
            i = j + 1
            continue
        m = DECL.match(l)
        if m:
            name = m.group(2)
            full = name if m.group(1) else '.'.join(ns_stack + [name])
            out.append((full, doc, l))
            doc = None
        elif l.strip() and not l.startswith(('@[', '--')):
            if not l.startswith(' '):
                doc = None
        i += 1
    return out


def namespace_prefix(full):
    return full if full.startswith('WeilClasses.') else 'WeilClasses.' + full


paper = []
external = []
for p in sorted((ROOT / 'WeilClasses').rglob('*.lean')):
    text = p.read_text()
    rel = p.relative_to(ROOT).as_posix()
    for full, doc, line in decls_with_docs(text):
        if '/External/HasseMinkowski/' in rel:
            # vendored code (jayyswan/hasse-minkowski, namespace `HasseMinkowski`): only the theorems
            # that this project cites are listed; its definitions are not hypotheses
            if line.startswith('theorem') and full in ('HasseMinkowski.meyer', 'HasseMinkowski.hasseMinkowski'):
                external.append(('HasseMinkowski', full))
            continue
        full = namespace_prefix(full).replace('WeilClasses.WeilClasses.', 'WeilClasses.')
        if '/External/' in rel and line.startswith('theorem'):
            # the cited results: docstring opens with a bold citation `**[Source, …]**`; helper
            # lemmas of the External proofs (prefixed `sa_`, `sb_`, …) are not listed
            short = full.split('.')[-1]
            if doc and re.match(r'/--\s*\*\*\[', doc) and not re.match(r's[a-z]_', short):
                src = rel.split('/External/')[1].split('/')[0]
                external.append((src, full))
            continue
        if '/External/' in rel and line.startswith('def') and re.search(r':\s*Prop\s*:=', line):
            # an assumed cited result (a named hypothesis of the statements that use it)
            src = rel.split('/External/')[1].split('/')[0]
            external.append((f'{src} (hypothesis)', full))
            continue
        if rel.endswith('WeilClasses/Defs.lean') and line.startswith('class'):
            external.append(('hypothesis', full))
            continue
        if doc:
            m = re.match(r'/--\s*\*\*((?:Lemma|Proposition|Theorem|Corollary|Remark|Example)\s+[\d.]+[^*]*|\([\d.]+\)[^*]*)\*\*',
                         doc)
            if m and line.startswith('theorem'):
                paper.append((m.group(1).strip(), full))


def key(label):
    nums = re.findall(r'\d+', label)
    return [int(x) for x in nums[:3]]


paper.sort(key=lambda p: key(p[0]))
chal = (ROOT / 'Challenge.lean').read_text()
sol = re.findall(r'^theorem (\S+)', chal.split('-- END SHARED DEFINITIONS')[1], re.M)

t = TEMPLATE.read_text()
t = t.replace('import all PaperName.Main\nimport all Solution\n',
              ''.join(f'import all {m}\n' for m in mods) + 'import all Solution\n')
t = t.replace('''meta def externalResults : List (String × Name) :=
  [("<cited theorem, short label>", ``PaperName.External.citedTheorem)]''',
              'meta def externalResults : List (String × Name) :=\n  [' +
              ',\n   '.join(f'("{s}", ``{n})' for s, n in external) + ']')
t = t.replace('''meta def paperResults : List (String × Name) :=
  [("Thm 1.1", ``PaperName.theorem1_1),
   ("Lemma 2.1", ``PaperName.lemma2_1)]''',
              'meta def paperResults : List (String × Name) :=\n  [' +
              ',\n   '.join(f'("{lab}", ``{n})' for lab, n in paper) + ']')
t = t.replace('''meta def solutionResults : List Name :=
  [``ChallengeNamespace.theorem_1_1]''',
              'meta def solutionResults : List Name :=\n  [' +
              ', '.join(f'``WeilClasses.Challenge.{n}' for n in sol) + ']')
t = t.replace("meta def isLibraryModule (m : Name) : Bool := (`PaperName).isPrefixOf m",
              "meta def isLibraryModule (m : Name) : Bool := (`WeilClasses).isPrefixOf m")
t = t.replace('PaperName/External/', 'WeilClasses/External/')
import sys
target = ROOT / 'scripts/Audit.lean'
if '--check' in sys.argv:
    if not target.exists() or target.read_text() != t:
        sys.exit('scripts/Audit.lean is out of date: run python3 scripts/gen_audit.py')
    print('scripts/Audit.lean is up to date')
else:
    target.write_text(t)
    print(f'{len(mods)} modules, {len(paper)} paper results, {len(external)} external/hypotheses, '
          f'{len(sol)} challenge theorems')
