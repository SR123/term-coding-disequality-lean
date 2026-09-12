"""Extract the complete paper, preserving TeX and LaTeX's own numbering."""
from pathlib import Path
import re, json, hashlib
from paths import MANUSCRIPT, PDFBUILD

ROOT = Path(__file__).resolve().parents[1]
source = (MANUSCRIPT/'paper3.tex').read_text()
aux = (PDFBUILD/'paper3.aux').read_text()
labels = {k:{'number':n,'page':p} for k,n,p in re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}\{([^}]+)\}',aux)}
citations = dict(re.findall(r'\\bibcite\{([^}]+)\}\{([^}]+)\}',aux))
abstract = re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}',source,re.S).group(1).strip()
body = source[source.index(r'\section{'):source.index(r'\bibliographystyle')]
tokens = re.compile(r'(\\section\{[^}]*\}|\\paragraph\{[^}]*\}|\\begin\{(?:definition|theorem|proposition|lemma|corollary|example|remark|proof)\}(?:\[[^\]]*\])?|\\end\{(?:definition|theorem|proposition|lemma|corollary|example|remark|proof)\})')
sections=[]; section=None; env=None; heading=''; counter=0; pending=[]
for part in tokens.split(body):
    if part.startswith(r'\section'):
        section={'number':len(sections)+1,'title':re.search(r'\{([^}]*)\}',part)[1],'blocks':[]}
        sections.append(section);counter=0
    elif part.startswith(r'\paragraph'):
        heading=re.search(r'\{([^}]*)\}',part)[1]
    elif part.startswith(r'\begin'):
        env=re.search(r'\{([^}]*)\}',part)[1]
        title=re.search(r'\[([^\]]*)\]',part)
        if env=='proof': heading=(title[1] if title else 'Proof')+'.'
        else:
            counter+=1;heading=f'{env.title()} {section["number"]}.{counter}.'
            if title:heading+=' '+title[1]+'.'
    elif part.startswith(r'\end'):
        if env=='proof' and section['blocks']:section['blocks'][-1]['qed']=True
        env=None
    else:
        for p in re.split(r'\n\s*\n',part.strip()):
            if not p.strip():continue
            for label in re.findall(r'\\label\{([^}]+)\}',p):
                if label.startswith('sec:'):
                    labels[label]['target']=f'section-{section["number"]}'
                else:pending.append(label)
            # A section label by itself is not a paragraph.
            if not re.sub(r'\\label\{[^}]*\}','',p).strip():continue
            bid=f's{section["number"]}-{len(section["blocks"])+1}'
            for label in pending:
                labels[label]['target']=bid
            block={'id':bid,'raw':p.strip(),'heading':heading,'kind':env or 'paragraph','labels':pending}
            section['blocks'].append(block);heading='';pending=[]
bbl=(PDFBUILD/'paper3.bbl').read_text()
bibliography=[]
for key,raw in re.findall(r'\\bibitem\{([^}]+)\}(.*?)(?=\\bibitem|\\end\{thebibliography\})',bbl,re.S):
    bibliography.append({'id':key,'number':citations[key],'raw':raw.strip().replace(r'\newblock','')})
data={'sourceHash':hashlib.sha256(source.encode()).hexdigest(),'abstract':abstract,'sections':sections,'labels':labels,'citations':citations,'bibliography':bibliography}
(ROOT/'content/paper.json').write_text(json.dumps(data,ensure_ascii=False,indent=2))
for section in sections:
    for b in section['blocks']:print(b['id'],b['heading'],re.sub(r'\s+',' ',b['raw'])[:120])
