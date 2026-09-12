from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import subprocess,json,os,time
root=Path(__file__).resolve().parents[1]
cfg=json.loads((root/'build/environment.json').read_text())
mods=['Audit','AuditClaude','AuditGeneral','AuditMachineRuntime','TypesGeneral','TypesMachineRuntime']
out=root/'build/audits';out.mkdir(exist_ok=True)
def run(m):
    start=time.monotonic()
    with (out/f'{m}.log').open('w') as f:
        p=subprocess.run([cfg['lean'],f'{m}.lean'],cwd=root/'Lean',env=dict(os.environ,LEAN_PATH=cfg['leanPath']),stdout=f,stderr=subprocess.STDOUT)
    log=(out/f'{m}.log').read_text()
    assert p.returncode==0,(m,p.returncode)
    assert 'sorryAx' not in log and 'PANIC' not in log and 'error:' not in log,m
    return m,{'exit':p.returncode,'seconds':round(time.monotonic()-start,2)}
with ThreadPoolExecutor(max_workers=2) as pool:report=dict(pool.map(run,mods))
(out/'report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
