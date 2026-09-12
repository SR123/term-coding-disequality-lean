"""Check prerendered files and asset references, including a Pages subpath."""
from pathlib import Path
import json,re,os,hashlib
ROOT=Path(__file__).resolve().parents[1];out=ROOT/'site/dist/client'
prefix=os.environ.get('PAPER_BASE_PATH','').rstrip('/')
html=(out/'index.html').read_text();assert 'One Unit Separates' in html and 'References' in html
edition=json.loads((ROOT/'site/app/edition.json').read_text())
for section in edition['sections']:
    assert 'id="section-'+str(section['number'])+'"' in html,('Missing prerendered section',section['number'])
    for block in section['blocks']:assert 'id="'+block['id']+'"' in html,('Missing prerendered paragraph',block['id'])
for entry in edition['bibliography']:assert 'id="bib-'+entry['id']+'"' in html,('Missing bibliography entry',entry['id'])
missing=[];checked=set()
def inspect_url(url,base):
    url=url.split('?')[0].split('#')[0]
    if not url or url.startswith(('data:','http:','https:','mailto:')):return
    if url.startswith('/'):
        if prefix:assert url.startswith(prefix+'/'),('Asset omits repository prefix',url)
        target=out/url.removeprefix(prefix).lstrip('/')
    else:target=base/url
    checked.add(str(target.relative_to(out)))
    if not target.is_file():missing.append(str(target))
for url in re.findall(r'(?:src|href)="([^"]+)"',html):
    if '_next/' in url or url.endswith('favicon.svg'):inspect_url(url,out)
for p in (out/'_next').rglob('*.css'):
    for url in re.findall(r'url\([\s\'"]*([^\s\)\'\"]+)',p.read_text()):inspect_url(url,p.parent)
assert not missing,missing
files=[p for p in out.rglob('*') if p.is_file()];largest=max(files,key=lambda p:p.stat().st_size)
assert largest.stat().st_size<90*1024*1024,('Split this unusually large web payload before release',str(largest))
index=json.loads((out/'proof/index.json').read_text());assert index['stats']['modules']==71
for e in index['declarations']:assert (out/'proof/declarations'/f'{e["key"]}.json').is_file(),e['name']
for p in ['paper3.pdf','paper3.tex','lean-source.zip','proof-evidence.zip','verification.json','README.md','LICENSES.txt']:assert (out/'paper'/p).is_file(),p
v=json.loads((out/'paper/verification.json').read_text());assert not v['draft']
assert hashlib.sha256((out/'paper/paper3.tex').read_bytes()).hexdigest()==v['manuscriptSha256']
result={'passed':True,'prefix':prefix,'prerenderedPaperPresent':True,'checkedAssets':len(checked),'missingAssets':missing,'files':len(files),'bytes':sum(p.stat().st_size for p in files),'largestFile':str(largest.relative_to(out)),'largestBytes':largest.stat().st_size,'proofStats':index['stats']}
name='static-subpath-check.json' if prefix else 'static-root-check.json'
(ROOT/'build'/name).write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
