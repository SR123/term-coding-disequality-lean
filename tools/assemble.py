"""Join authored correspondence with machine-exported declarations and source states.

The output is static JSON. This script never invents a type, dependency or proof state.
"""
from pathlib import Path
from collections import defaultdict,deque
import argparse,json,hashlib,shutil,tomllib,zipfile,re,datetime
from concurrent.futures import ThreadPoolExecutor,as_completed
from paths import MANUSCRIPT, PDFBUILD
from trace_utils import is_example_command

ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser();parser.add_argument('--exports',default='build/exports');parser.add_argument('--output',default='site/public/proof');parser.add_argument('--draft',action='store_true');args=parser.parse_args()
export=ROOT/args.exports
raw_index=json.loads((export/'index.json').read_text())
entries=raw_index['declarations'];by_name={e['name']:e for e in entries}
assert len(by_name)==len(entries),'Duplicate declarations'
assert len({e['key'] for e in entries})==len(entries),'Hash collision in output filenames'
assert not raw_index['missing'],raw_index['missing']
if not args.draft:assert raw_index.get('sourceReferencesComplete',False),'The final source-reference export is required.'
modules=tomllib.loads((ROOT/'Lean/lakefile.toml').read_text())['defaultTargets']
cfg=json.loads((ROOT/'build/environment.json').read_text())
packages=Path(cfg['packages']);sysroot=Path(cfg['lean']).parent.parent
source_roots=[Path(cfg.get('projectSource',ROOT/'Lean')),sysroot/'src/lean']+[p for p in packages.iterdir() if p.is_dir()]
sources={};source_paths={}
for m in {e['module'] for e in entries}|set(modules):
    cached=Path(cfg['moduleSourceCache'])/f'{m}.lean' if cfg.get('moduleSourceCache') else None
    if cached and cached.is_file():
        source_paths[m]=cached;continue
    for base in source_roots:
        p=base/Path(*m.split('.')).with_suffix('.lean')
        if p.is_file():
            source_paths[m]=p;break
def read_source(m):
    for attempt in range(4):
        try:return m,source_paths[m].read_bytes().decode('utf-8')
        except TimeoutError:print('Retrying source read:',m,attempt+1,flush=True)
    raise RuntimeError('Cannot read source '+m)
with ThreadPoolExecutor(max_workers=8) as pool:
    for future in as_completed([pool.submit(read_source,m) for m in source_paths]):
        m,text=future.result();sources[m]=text
print('Read',len(sources),'complete source modules.',flush=True)
refs=defaultdict(list);steps=defaultdict(list);extra_steps=defaultdict(list);extra_refs=defaultdict(set);example_commands=defaultdict(list);all_holes=0;total_tactics=0;total_references=0
for m in modules:
    f=Path(cfg.get('tracePath',ROOT/'build/traces'))/f'{m}.json'
    if not f.exists():
        if args.draft:continue
        raise RuntimeError('Missing elaboration trace: '+m)
    tr=json.loads(f.read_text());goal_intern={}
    source=sources[m].encode()
    for r in tr['rows']:
        if r['kind']=='tactic':
            for side in ['before','after']:
                for i,g in enumerate(r[side]):
                    assert set(g)=={'id','text'}
                    key=(g['id'],g['text'])
                    r[side][i]=goal_intern.setdefault(key,g)
        if r['kind']=='unresolvedInfo':all_holes+=1;continue
        decl=r.get('declaration');target=by_name.get(decl)
        named=bool(target and target['project'] and target['module']==m)
        if r['kind']=='reference':
            total_references+=1
            if is_example_command(r,source):example_commands[m].append(r)
            elif named:refs[decl].append(r)
            else:extra_refs[m].add(r['name'])
        else:
            total_tactics+=1
            for side in ['before','after']:
                assert all(g['text']!='unknown goal' for g in r[side]),('Unknown goal',m,r['id'],side)
            r['code']=source[r['range']['start']['byte']:r['range']['end']['byte']].decode()
            if named:steps[decl].append(r)
            else:extra_steps[m].append(r)
assert not all_holes,all_holes

notes=json.loads((ROOT/'content/notes.json').read_text())
aliases={};missing_aliases=[]
for key in sorted({r for n in notes.values() for r in n['sources']}):
    mod,short=key.split(':',1)
    candidates=[e['name'] for e in entries if e['module']==mod and (e['name']==short or e['name'].endswith('.'+short))]
    if len(candidates)!=1:
        if args.draft:continue
        missing_aliases.append([key,candidates]);continue
    aliases[key]=candidates[0]
assert not missing_aliases,missing_aliases

def pack_steps(raw):
    pool=[];goal_ids={};encoded_steps=[]
    for step in raw:
        encoded=dict(step)
        for side in ['before','after']:
            indices=[]
            for goal in step[side]:
                key=(goal['id'],goal['text'])
                if key not in goal_ids:
                    goal_ids[key]=len(pool);pool.append(goal)
                indices.append(goal_ids[key])
            assert [pool[i] for i in indices]==step[side]
            encoded[side]=indices
        encoded_steps.append(encoded)
    return encoded_steps,pool

out=ROOT/args.output;(out/'declarations').mkdir(parents=True,exist_ok=True);(out/'modules').mkdir(exist_ok=True)
deps={};axiom_names=set();bad_nodes=[];missing_refs=[];source_ranges=0;total_nodes=0
for e in entries:
    d=json.loads((export/'declarations'/f'{e["key"]}.json').read_text())
    name=d['name'];deps[name]=d['dependencies'];total_nodes+=len(d['nodes'])
    if not d['unsafe'] and d['kind'] in ['theorem','definition','opaque']:
        assert d['value'] is not None,('Missing declaration body',name)
    if d['kind']=='axiom':axiom_names.add(name)
    required=[]
    for i,node in enumerate(d['nodes']):
        if node[0] in ['metavariable','free']:bad_nodes.append([name,i,node])
        for j in ({'apply':[1,2],'lambda':[2,3],'forall':[2,3],'let':[2,3,4],'metadata':[1],'projection':[3]}.get(node[0],[])):
            assert 0<=node[j]<i,('Not a well-founded expression DAG',name,i,node)
        tag=node[0]
        need=node[1]+1 if tag=='bound' else 0
        if tag=='apply':need=max(required[node[1]],required[node[2]])
        elif tag in ['lambda','forall']:need=max(required[node[2]],max(0,required[node[3]]-1))
        elif tag=='let':need=max(required[node[2]],required[node[3]],max(0,required[node[4]]-1))
        elif tag=='metadata':need=required[node[1]]
        elif tag=='projection':need=required[node[3]]
        required.append(need)
    for root_id in [d['type']]+([d['value']] if d['value'] is not None else [])+([r['rhs'] for r in d['extra']['rules']] if isinstance(d.get('extra'),dict) and 'rules' in d['extra'] else []):
        assert required[root_id]==0,('Unbound de Bruijn index',name,root_id)
    for dep in d['dependencies']:assert dep in by_name,('Missing dependency',name,dep)
    if d['module'] in sources and d.get('range'):
        r=d['range'];lines=sources[d['module']].splitlines();start=r['line'];end=r['endLine']
        if 1<=start<=end<=len(lines):
            d['source']={'code':'\n'.join(lines[start-1:end]),'start':start,'end':end};source_ranges+=1
    if e['project']:
        # Store repeated goal states once, preserving every step and exact text.
        # Nested tactic traces otherwise repeat the same long local contexts.
        d['steps'],d['stepGoalPool']=pack_steps(steps.get(name,[]))
        d['references']=[]
        for r in refs.get(name,[]):
            if r['name'] in by_name:d['references'].append(r)
            else:missing_refs.append([name,r['name']])
        if d.get('source'):
            # Preserve each source line; hyperlinks use exact byte spans from Lean.
            lines=sources[d['module']].splitlines(keepends=True);starts=[];offset=0
            for line in lines:starts.append(offset);offset+=len(line.encode())
            marked=[]
            for ln in range(d['source']['start'],d['source']['end']+1):
                line=lines[ln-1].rstrip('\n');base=starts[ln-1];raw=line.encode();pos=0;segments=[]
                candidates=[r for r in d['references'] if r['range']['start']['line']==ln and r['range']['end']['line']==ln]
                candidates.sort(key=lambda r:(r['range']['start']['byte'],r['range']['end']['byte']-r['range']['start']['byte']))
                for r in candidates:
                    a=r['range']['start']['byte']-base;b=r['range']['end']['byte']-base
                    if a<pos or b<=a or b>len(raw):continue
                    if a>pos:segments.append({'text':raw[pos:a].decode()})
                    segments.append({'text':raw[a:b].decode(),'name':r['name']});pos=b
                if pos<len(raw):segments.append({'text':raw[pos:].decode()})
                marked.append(segments)
            d['source']['lines']=marked
    (out/'declarations'/f'{e["key"]}.json').write_text(json.dumps(d,ensure_ascii=False,separators=(',',':')))
assert not bad_nodes,('Unresolved expression nodes',bad_nodes[:10])
if not args.draft:assert not missing_refs,('References absent from export',missing_refs[:30])

# Propagate axiom sets to a fixed point; inductive families may refer to their constructors.
reverse=defaultdict(set)
for n,ds in deps.items():
    for dep in ds:reverse[dep].add(n)
axioms={n:set() for n in by_name}
for ax in axiom_names:
    seen=set();queue=deque([ax])
    while queue:
        n=queue.popleft()
        if n in seen:continue
        seen.add(n);axioms[n].add(ax);queue.extend(reverse[n])
for e in entries:
    p=out/'declarations'/f'{e["key"]}.json';d=json.loads(p.read_text());d['axioms']=sorted(axioms[e['name']]);p.write_text(json.dumps(d,ensure_ascii=False,separators=(',',':')))
for m,text in sources.items():(out/'modules'/f'{m}.lean').write_text(text)
for m in modules:
    encoded,pool=pack_steps(extra_steps[m])
    names=sorted(extra_refs[m]);missing=[n for n in names if n not in by_name]
    if not args.draft:assert not missing,('Missing module reference',m,missing)
    payload={'steps':encoded,'stepGoalPool':pool,'references':[n for n in names if n in by_name],'exampleCommands':example_commands[m]}
    (out/'modules'/f'{m}.steps.json').write_text(json.dumps(payload,ensure_ascii=False,separators=(',',':')))
assert total_tactics==sum(map(len,steps.values()))+sum(map(len,extra_steps.values()))
stats={'declarations':len(entries),'projectDeclarations':sum(e['project'] for e in entries),'modules':len(modules),'libraryModules':len(sources)-len(modules),'tactics':total_tactics,'moduleLevelTactics':sum(map(len,extra_steps.values())),'sourceReferences':total_references,'checkedUnnamedExamples':sum(map(len,example_commands.values())),'expressionNodes':total_nodes,'sourceRanges':source_ranges,'explanations':len(notes)}
index={'declarations':entries,'aliases':aliases,'modules':modules,'stats':stats}
(out/'index.json').write_text(json.dumps(index,ensure_ascii=False,separators=(',',':')))
paper_out=ROOT/'site/public/paper';paper_out.mkdir(exist_ok=True)
shutil.copy2(PDFBUILD/'paper3.pdf',paper_out/'paper3.pdf')
shutil.copy2(MANUSCRIPT/'paper3.tex',paper_out/'paper3.tex')
shutil.copy2(MANUSCRIPT/'references.bib',paper_out/'references.bib')
with zipfile.ZipFile(paper_out/'lean-source.zip','w',zipfile.ZIP_DEFLATED) as z:
    for p in sorted((ROOT/'Lean').iterdir()):
        if p.is_file():z.write(p,'Lean/'+p.name)
    for p in sorted((ROOT/'evidence').rglob('*')):
        if p.is_file():z.write(p,'evidence/'+str(p.relative_to(ROOT/'evidence')))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest={str(p.relative_to(ROOT)):sha(p) for p in sorted((ROOT/'Lean').iterdir()) if p.is_file()}
verification={'generatedUTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'draft':args.draft,'manuscriptSha256':sha(MANUSCRIPT/'paper3.tex'),'leanVersion':'4.26.0','mathlibCommit':'2df2f0150c275ad53cb3c90f7c98ec15a56a1a67','stats':stats,'missingDependencies':raw_index['missing'],'unresolvedInfo':all_holes,'unresolvedExpressions':bad_nodes,'missingSourceReferences':missing_refs,'axiomDeclarations':sorted(axiom_names),'projectAxioms':sorted(set().union(*(axioms[e['name']] for e in entries if e['project']))),'leanSourceSha256':manifest,'externalInputs':['Fixed-presentation finite-group noncomputability (Slobodskoi–Bridson–Wilton), an explicit hypothesis.','The standard polynomial RAM-to-multitape-Turing-machine simulation is not formalised.'],'correspondence':'English explanations and paper-to-declaration links are authored, not kernel-certified.'}
(paper_out/'verification.json').write_text(json.dumps(verification,ensure_ascii=False,indent=2))
(ROOT/'build/assembly-report.json').write_text(json.dumps(verification,ensure_ascii=False,indent=2))
print(json.dumps(stats,indent=2));print('Axioms:',sorted(axiom_names))
