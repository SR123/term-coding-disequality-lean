"""Integrity, correspondence, link, source-identity and export-closure checks."""
from pathlib import Path
import json,hashlib,re,tomllib
from paths import ROOT,MANUSCRIPT
load=lambda p:json.loads((ROOT/p).read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
edition=load('site/app/edition.json');index=load('site/public/proof/index.json');v=load('site/public/paper/verification.json')
assert not v['draft'],'A draft export is not a release'
assert edition['sourceHash']==v['manuscriptSha256']==sha(MANUSCRIPT/'paper3.tex')
assert load('content/correspondence.json')['manuscriptSha256']==v['manuscriptSha256'],'The manuscript changed: inspect and update the authored correspondence before releasing.'
assert len(edition['sections'])==8
blocks=[b for s in edition['sections'] for b in s['blocks']]
assert len(blocks)==72
ids={b['id'] for b in blocks}|{'abstract','paper','references'}|{'section-'+str(s['number']) for s in edition['sections']}|{'bib-'+b['id'] for b in edition['bibliography']}
notes=edition['notes'];seen=set();active=set()
def visit(n):
    assert n in notes,('Missing explanation',n)
    assert n not in active,('Circular explanation chain',n)
    if n in seen:return
    active.add(n);node=notes[n]
    if not node['children'] and not node['sources']:assert node['kind']=='scope',('Unlinked mathematical endpoint',n)
    for child in node['children']:visit(child)
    for ref in node['sources']:assert ref in index['aliases'],('Missing formal target',n,ref)
    active.remove(n);seen.add(n)
for bid in [b['id'] for b in blocks]+['abstract']:visit(bid)
for text in [edition['abstractHtml']]+[b['html']+b['headingHtml'] for b in blocks]+[b['html'] for b in edition['bibliography']]+[n['html']+n['titleHtml'] for n in notes.values()]:
    for target in re.findall(r'href="#([^"]+)"',text):assert target in ids,('Broken paper reference',target)
    assert 'katex-error' not in text
names={e['name'] for e in index['declarations']}
assert set(index['aliases'].values())<=names
assert not v['missingDependencies'] and not v['missingSourceReferences']
assert not v['unresolvedInfo'] and not v['unresolvedExpressions']
assert set(v['projectAxioms'])<={'propext','Classical.choice','Quot.sound'},v['projectAxioms']
for relative,digest in v['leanSourceSha256'].items():assert sha(ROOT/relative)==digest,relative
identity=load('evidence/CLAUDE_SOURCE_IDENTITY.json')
for name,digest in identity['files'].items():assert sha(ROOT/'Lean'/name)==digest,('Claude source altered',name)
mods=tomllib.loads((ROOT/'Lean/lakefile.toml').read_text())['defaultTargets'];report=load('build/trace-report.json')
assert len(mods)==71
for m in mods:
    assert report[m]['exit']==0 and report[m]['unresolvedInfo']==0,m
    assert report[m]['sourceSha256']==sha(ROOT/'Lean'/f'{m}.lean'),m
    log=(ROOT/'build/logs'/f'{m}.log').read_text()
    assert 'PANIC' not in log and 'error:' not in log,m
assert v['stats']['tactics']==sum(report[m]['tactics'] for m in mods),'Recorded proof steps were omitted during assembly'
assert v['stats']['sourceReferences']==sum(report[m]['references'] for m in mods),'Recorded source references were omitted during assembly'
for m in mods:
    assert (ROOT/'site/public/proof/modules'/f'{m}.lean').read_bytes()==(ROOT/'Lean'/f'{m}.lean').read_bytes(),('Module download altered',m)
    assert (ROOT/'site/public/proof/modules'/f'{m}.steps.json').is_file(),('Missing module-level proof evidence',m)
audits=load('build/audits/report.json');assert len(audits)==6 and all(x['exit']==0 for x in audits.values())
for p in ['paper3.pdf','paper3.tex','references.bib','lean-source.zip','README.md','LICENSES.txt']:
    assert (ROOT/'site/public/paper'/p).is_file(),p
result={'passed':True,'sections':8,'paragraphs':len(blocks),'abstract':True,'bibliographyEntries':len(edition['bibliography']),'reachableExplanations':len(seen),'formalCorrespondenceLinks':len(index['aliases']),'leanModules':len(mods),'claudeFilesUnchanged':len(identity['files']),'auditCommands':len(audits),'axioms':v['projectAxioms'],'proofStats':v['stats'],'manuscriptSha256':v['manuscriptSha256'],'typescript':'Run separately with npm run typecheck','staticBuild':'Run separately with npm run build'}
(ROOT/'build/check-report.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
