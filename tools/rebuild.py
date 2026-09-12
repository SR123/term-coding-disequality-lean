"""Reproduce the paper, proof exports, audits, correspondence and static site.

Requires Python 3.11+, the pinned Lean via elan/Lake, Node 22.13+, and latexmk.
Run from any directory: python3 tools/rebuild.py
"""
from pathlib import Path
import subprocess,sys,os
from paths import ROOT,MANUSCRIPT
def run(args,cwd=ROOT):
    print('+',' '.join(map(str,args)),flush=True);subprocess.run(list(map(str,args)),cwd=cwd,check=True)
run(['lake','exe','cache','get'],ROOT/'Lean')
run(['lake','build'],ROOT/'Lean')
for script in ['configure.py','trace_all.py','export_all.py','audit_all.py']:
    run([sys.executable,ROOT/'tools'/script])
(ROOT/'build/paper').mkdir(exist_ok=True)
run(['latexmk','-pdf','-interaction=nonstopmode','-halt-on-error','-outdir='+str(ROOT/'build/paper'),'paper3.tex'],MANUSCRIPT)
for script in ['paper.py','notes.py','assemble.py']:
    run([sys.executable,ROOT/'tools'/script])
run(['npm','ci'],ROOT/'site')
run(['node',ROOT/'tools/render.mjs'])
run([sys.executable,ROOT/'tools/check.py'])
run(['npm','run','typecheck'],ROOT/'site')
# Record the successful check for the downloadable evidence bundle.
(ROOT/'build/typecheck-final.log').write_text('npm run typecheck: passed\n')
run([sys.executable,ROOT/'tools/publish_evidence.py'])
run(['npm','run','build'],ROOT/'site')
run([sys.executable,ROOT/'tools/static_check.py'])
print('Static site:',ROOT/'site/dist/client')
