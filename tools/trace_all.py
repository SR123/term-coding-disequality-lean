from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
import subprocess,os,json,hashlib,time,tomllib
root=Path(__file__).resolve().parents[1]
cfg=json.loads((root/'build/environment.json').read_text())
env=dict(os.environ,LEAN_PATH=cfg['leanPath'])
modules=tomllib.loads((root/'Lean/lakefile.toml').read_text())['defaultTargets']
deps={}
for m in modules:
 text=(root/'Lean'/f'{m}.lean').read_text()
 deps[m]={v for line in text.splitlines() if line.startswith('import ') for v in line[7:].split() if v in modules}
report=json.loads((root/'build/trace-report.json').read_text()) if (root/'build/trace-report.json').exists() else {}
done={m for m,item in report.items() if item['exit']==0 and item['sourceSha256']==hashlib.sha256((root/'Lean'/f'{m}.lean').read_bytes()).hexdigest()}
pending=set(modules)-done;running={}
def build(m):
 start=time.monotonic()
 log=root/'build/logs'/f'{m}.log'
 with log.open('w') as f:
  p=subprocess.run([cfg['lean'],'--run',str(root/'tools/ExportTrace.lean'),f'{m}.lean',str(root/'build/traces'/f'{m}.json'),str(root/'build/lib'/f'{m}.olean')],cwd=root/'Lean',env=env,stdout=f,stderr=subprocess.STDOUT)
 item={'exit':p.returncode,'seconds':round(time.monotonic()-start,2),'sourceSha256':hashlib.sha256((root/'Lean'/f'{m}.lean').read_bytes()).hexdigest()}
 if p.returncode==0:
  trace=json.loads((root/'build/traces'/f'{m}.json').read_text())
  item['tactics']=sum(x['kind']=='tactic' for x in trace['rows'])
  item['references']=sum(x['kind']=='reference' for x in trace['rows'])
  item['unresolvedInfo']=sum(x['kind']=='unresolvedInfo' for x in trace['rows'])
 return item
with ThreadPoolExecutor(max_workers=2) as pool:
 while pending or running:
  available=sorted(m for m in pending if deps[m]<=done)
  while available and len(running)<2:
   m=available.pop(0);pending.remove(m);running[pool.submit(build,m)]=m
  if not running:raise RuntimeError('Module dependency cycle')
  complete,_=wait(running,return_when=FIRST_COMPLETED)
  for future in complete:
   m=running.pop(future);item=future.result();report[m]=item
   (root/'build/trace-report.json').write_text(json.dumps(report,indent=2))
   print(m,json.dumps(item),flush=True)
   if item['exit']!=0:raise RuntimeError(f'Elaboration failed: {m}; see build/logs/{m}.log')
   done.add(m)
print('All modules elaborated and traced.',flush=True)
