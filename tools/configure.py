"""Configure exporters from the pinned Lake environment, without machine-specific paths."""
from pathlib import Path
import subprocess,json,os
root=Path(__file__).resolve().parents[1];project=root/'Lean'
def lake(*args):return subprocess.check_output(['lake','env',*args],cwd=project,text=True).strip()
prefix=Path(lake('lean','--print-prefix'))
paths=[str(root/'build/lib')]+[str((project/p).resolve()) for p in lake('printenv','LEAN_PATH').split(os.pathsep) if p]
for kind in ['lib','traces','logs','exports']:(root/'build'/kind).mkdir(parents=True,exist_ok=True)
cfg={'lean':str(prefix/'bin/lean'),'leanPath':os.pathsep.join(paths),'packages':str(project/'.lake/packages')}
(root/'build/environment.json').write_text(json.dumps(cfg,indent=2));print('Configured Lean',subprocess.check_output([str(prefix/'bin/lean'),'--version'],text=True).strip())
