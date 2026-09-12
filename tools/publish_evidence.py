"""Prepare downloadable evidence of local checks; this does not publish a site."""
from pathlib import Path
import shutil,json,zipfile,hashlib
ROOT=Path(__file__).resolve().parents[1]
report=json.loads((ROOT/'build/check-report.json').read_text())
assert report['passed'] and report['leanModules']==71
out=ROOT/'evidence/LOCAL_2026-09-11';out.mkdir(exist_ok=True)
for name in ['trace-report.json','assembly-report.json','typesetting-report.json','check-report.json','kernel-export.log','typecheck-final.log']:
    shutil.copy2(ROOT/'build'/name,out/name)
for name in ['audits','logs']:
    shutil.copytree(ROOT/'build'/name,out/name,dirs_exist_ok=True)
if (ROOT/'build/cache-test/equivalence.json').exists():shutil.copy2(ROOT/'build/cache-test/equivalence.json',out/'goal-cache-equivalence.json')
(out/'README.md').write_text("""# Independent local verification — 11 September 2026

All 71 mathematical/algorithmic modules were elaborated from Claude's unchanged source with the pinned Lean 4.26 toolchain and Mathlib dependency. Six audit/type commands were then run against these local modules. Logs include harmless linter warnings where Lean emitted them; elaboration errors, information-tree holes, admissions and missing proof dependencies are rejected by the release checks.

The trace exporter waits for elaboration tasks, resolves their information trees and uses enlarged resource budgets for documentation. It resets the accumulated heartbeat counter before exporting suggestion metadata, after checking and tracing. An immutable-snapshot cache avoids repeated pretty-printing. Metavariable-free goals can share the display for their unchanged declaration; other goals use the complete metavariable snapshot. The Core and MLib3 equivalence checks compare recorded text, spans and references against the earlier exporters. This tooling is never imported by the proof project.

The kernel-export log preserves preliminary documentation attempts, including an incomplete local IR cache and the initial treatment of temporary unnamed-example markers. The final successful export and closure checks govern this release. These documentation issues were resolved without changing Claude's formal source or admitting any proof.

The check report also verifies the manuscript correspondence targets, full dependency closure, unchanged source hashes, every mathematical expression node's well-founded structure and closed binders, and the three standard foundational axioms. English explanations and paper-to-statement correspondence remain authored material for mathematical review. The external finite-group theorem is an explicit hypothesis; RAM-to-Turing-machine simulation remains unformalised.
""")
if (ROOT/'build/cache-test/closed-equivalence.json').exists():shutil.copy2(ROOT/'build/cache-test/closed-equivalence.json',out/'closed-goal-cache-equivalence.json')
if (ROOT/'build/ordinary/report.json').exists():shutil.copytree(ROOT/'build/ordinary',out/'ordinary-machine-checks',ignore=shutil.ignore_patterns('lib'),dirs_exist_ok=True)
pub=ROOT/'site/public/paper';shutil.copy2(ROOT/'README.md',pub/'README.md')
with zipfile.ZipFile(pub/'proof-evidence.zip','w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
    for p in sorted((ROOT/'evidence').rglob('*')):
        if p.is_file():z.write(p,'evidence/'+str(p.relative_to(ROOT/'evidence')))
with zipfile.ZipFile(pub/'lean-source.zip','w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
    for p in sorted((ROOT/'Lean').iterdir()):
        if p.is_file():z.write(p,'Lean/'+p.name)
    for p in sorted((ROOT/'evidence').rglob('*')):
        if p.is_file():z.write(p,'evidence/'+str(p.relative_to(ROOT/'evidence')))
v=json.loads((pub/'verification.json').read_text())
v['evidence']={'archive':'proof-evidence.zip','sha256':hashlib.sha256((pub/'proof-evidence.zip').read_bytes()).hexdigest(),'localChecks':'evidence/LOCAL_2026-09-11/check-report.json','localAuditCommands':6,'allLocalModulesElaborated':True}
(pub/'verification.json').write_text(json.dumps(v,ensure_ascii=False,indent=2))
print('Prepared downloadable local and Claude evidence.')
