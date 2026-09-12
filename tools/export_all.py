"""Export exact declaration bodies, extending a fingerprinted dependency-closed cache.
--available-traces permits an early pass while the last display traces are running.
A later ordinary invocation adds every remaining source-reference target.
"""
from pathlib import Path
import argparse,json,subprocess,os,tomllib,hashlib,shutil,time
from trace_utils import is_example_command
root=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--available-traces',action='store_true');args=p.parse_args()
cfg=json.loads((root/'build/environment.json').read_text());mods=tomllib.loads((root/'Lean/lakefile.toml').read_text())['defaultTargets']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
objects={}
for m in mods:
    for folder in cfg['leanPath'].split(os.pathsep):
        obj=Path(folder)/f'{m}.olean'
        if obj.is_file():objects[m]=sha(obj);break
    else:raise RuntimeError('Missing checked module '+m)
exporter=Path(cfg.get('kernelExporter',root/'tools/ExportKernel.lean'))
fingerprint={'objects':objects,'tool':sha(exporter),'leanBinary':sha(Path(cfg['lean'])),'dependencyManifest':sha(Path(cfg.get('projectSource',root/'Lean'))/'lake-manifest.json')}
export=root/'build/exports';marker=export/'fingerprint.json'
if export.exists() and (not marker.exists() or json.loads(marker.read_text())!=fingerprint):
    export.rename(root/'build'/('exports-previous-'+str(time.time_ns())))
export.mkdir(exist_ok=True);(export/'declarations').mkdir(exist_ok=True)
old=json.loads((export/'index.json').read_text()) if (export/'index.json').exists() else {'declarations':[],'missing':[],'rootModules':mods}
assert not old['missing'] and old['rootModules']==mods
names=set();included=[]
for m in mods:
    path=Path(cfg.get('tracePath',root/'build/traces'))/f'{m}.json'
    if not path.exists():
        if args.available_traces:continue
        raise RuntimeError('Missing complete trace '+m)
    tr=json.loads(path.read_text());included.append(m)
    source=(Path(cfg.get('projectSource',root/'Lean'))/f'{m}.lean').read_bytes()
    names.update(r['name'] for r in tr['rows'] if r['kind']=='reference' and not is_example_command(r,source))
reference_file=root/'build/reference-names.txt';reference_file.write_text('\n'.join(sorted(names)))
cached_file=root/'build/cached-declarations.txt';cached_file.write_text('\n'.join(e['name'] for e in old['declarations']))
for e in old['declarations']:assert (export/'declarations'/f'{e["key"]}.json').is_file()
stage=root/'build'/('exports-stage-'+str(time.time_ns()));stage.mkdir()
cmd=[cfg['lean'],'--run',str(exporter),str(stage),str(reference_file),str(cached_file),*mods]
log=root/'build/kernel-export.log'
with log.open('a') as out:
    out.write('\nEXPORT PASS: '+str(len(included))+' source traces; '+str(len(old['declarations']))+' cached declarations\n');out.flush()
    result=subprocess.run(cmd,cwd=root/'Lean',env=dict(os.environ,LEAN_PATH=cfg['leanPath']),stdout=out,stderr=subprocess.STDOUT)
assert result.returncode==0,('Kernel export failed; see log',result.returncode)
new=json.loads((stage/'index.json').read_text());assert not new['missing']
assert not ({e['name'] for e in old['declarations']}&{e['name'] for e in new['declarations']})
for f in (stage/'declarations').iterdir():
    assert not (export/'declarations'/f.name).exists(),('Filename hash collision',f.name)
    f.rename(export/'declarations'/f.name)
combined={'declarations':old['declarations']+new['declarations'],'missing':[],'rootModules':mods,'sourceTraceModules':included,'sourceReferencesComplete':len(included)==len(mods)}
(export/'index.json').write_text(json.dumps(combined,separators=(',',':')));marker.write_text(json.dumps(fingerprint,indent=2));shutil.rmtree(stage)
print(json.dumps({'newDeclarations':len(new['declarations']),'totalDeclarations':len(combined['declarations']),'sourceTraces':len(included),'sourceReferencesComplete':combined['sourceReferencesComplete']}),flush=True)
