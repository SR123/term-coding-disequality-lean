import fs from 'node:fs';
import {createRequire} from 'node:module';
const require=createRequire(new URL('../site/package.json',import.meta.url));
const katex=require('katex');
const root=new URL('../',import.meta.url);
const read=p=>JSON.parse(fs.readFileSync(new URL(p,root),'utf8'));
const paper=read('content/paper.json');const notes=read('content/notes.json');
const esc=s=>s.replaceAll('&','&amp;').replaceAll('<','&lt;').replaceAll('>','&gt;').replaceAll('"','&quot;');
let formulas=0;const errors=[];
function group(text,start){
  if(text[start]!=='{')throw Error('Expected brace: '+text.slice(start,start+50));
  let depth=1,end=start+1;
  for(;end<text.length&&depth;end++){if(text[end]==='{'&&text[end-1]!=='\\')depth++;if(text[end]==='}'&&text[end-1]!=='\\')depth--;}
  return [text.slice(start+1,end-1),end];
}
function prose(text){
  let html='',i=0;
  while(i<text.length){
    if(text[i]==='{'){
      let [value,end]=group(text,i);html+=value.startsWith('\\em ')?'<em>'+prose(value.slice(4))+'</em>':prose(value);i=end;continue;
    }
    if(text[i]!=='\\'){html+=esc(text[i]==='~'?'\u00a0':text[i]);i++;continue;}
    const command=/^\\([A-Za-z]+|.)/.exec(text.slice(i));if(!command){html+='\\';i++;continue;}
    const name=command[1];i+=command[0].length;
    if(name==='\\'){html+='<br/>';continue;}
    if(name==='_'){html+='_';continue;}
    if(name==='o'){html+='ø';continue;}
    if(name==='noindent'||name==='newblock')continue;
    if(name==='PaperThreeLeanGitHub'){html+='<span class="publication-pending">[GitHub URL to be added]</span>';continue;}
    if(name==='PaperThreeLeanDOI'){html+='<span class="publication-pending">[DOI to be added]</span>';continue;}
    let optional='';
    if(name==='cite'&&text[i]==='['){let end=text.indexOf(']',i);optional=text.slice(i+1,end);i=end+1;}
    if(['emph','textit','textbf','texttt','textsc','label','ref','eqref','cite','href','url','begin','end'].includes(name)){
      let [value,end]=group(text,i);i=end;
      if(name==='label')continue;
      if(name==='begin'||name==='end'){
        if(value!=='quote')throw Error('Unknown prose environment '+value);
        html+=name==='begin'?'<blockquote>':'</blockquote>';continue;
      }
      if(name==='ref'||name==='eqref'){
        const l=paper.labels[value];if(!l?.target)throw Error('Missing label '+value);
        html+=`<a class="paper-reference" href="#${l.target}">${name==='eqref'?'('+l.number+')':l.number}</a>`;continue;
      }
      if(name==='cite'){
        html+='['+value.split(',').map(key=>{if(!paper.citations[key])throw Error('Missing citation '+key);return `<a href="#bib-${key}">${paper.citations[key]}</a>`;}).join(', ')+(optional?', '+prose(optional):'')+']';continue;
      }
      if(name==='href'){
        const [label,after]=group(text,i);i=after;
        if(!/^https:\/\//.test(value))throw Error('Invalid URL');
        html+=`<a href="${esc(value)}" target="_blank" rel="noreferrer">${prose(label)}</a>`;continue;
      }
      if(name==='url'){html+=`<a href="${esc(value)}">${esc(value)}</a>`;continue;}
      const tag={emph:'em',textit:'em',textbf:'strong',texttt:'code',textsc:'span'}[name];
      html+=`<${tag}${name==='textsc'?' class="small-caps"':''}>${prose(value)}</${tag}>`;continue;
    }
    throw Error('Unrecognised prose command \\'+name+' in '+text);
  }
  return html.replaceAll('---','—').replaceAll('--','–').replaceAll('``','“').replaceAll("''",'”');
}
function math(tex,display){
  formulas++;
  tex=tex.replace(/\\label\{([^}]+)\}/g,(_,key)=>'\\tag{'+paper.labels[key].number+'}');
  try{return `<span class="${display?'display-math':'inline-math'}">${katex.renderToString(tex,{displayMode:display,throwOnError:true,strict:'error',trust:false,macros:{'\\DD':'D','\\Spec':'\\operatorname{Spec}','\\Sym':'\\operatorname{Sym}','\\id':'\\operatorname{id}','\\N':'\\mathbb{N}'}})}</span>`;}
  catch(e){errors.push({tex,error:e.message});return '';}
}
function rich(text){
  const regex=/(\$[^$]*?\$|\\\[[\s\S]*?\\\]|\\begin\{(?:align|equation)\}[\s\S]*?\\end\{(?:align|equation)\})/g;
  return text.split(regex).map(part=>{
    if(part.startsWith('$'))return math(part.slice(1,-1),false);
    if(part.startsWith('\\['))return math(part.slice(2,-2),true);
    if(part.startsWith('\\begin{align}'))return part.replace(/^\\begin\{align\}|\\end\{align\}$/g,'').split('\\\\').map(row=>math(row.replaceAll('&',''),true)).join('');
    if(part.startsWith('\\begin{equation}'))return math(part.replace(/^\\begin\{equation\}|\\end\{equation\}$/g,''),true);
    return prose(part);
  }).join('');
}
paper.abstractHtml=rich(paper.abstract);
for(const s of paper.sections)for(const b of s.blocks){b.html=rich(b.raw);b.headingHtml=rich(b.heading);}
for(const b of paper.bibliography)b.html=rich(b.raw);
for(const n of Object.values(notes)){n.html=rich(n.body);n.titleHtml=rich(n.title);}
if(errors.length){console.error(errors);process.exit(1);}
fs.writeFileSync(new URL('site/app/edition.json',root),JSON.stringify({...paper,notes}));
fs.writeFileSync(new URL('build/typesetting-report.json',root),JSON.stringify({formulas,errors,paragraphs:paper.sections.reduce((a,s)=>a+s.blocks.length,0),explanations:Object.keys(notes).length},null,2));
console.log(`Typeset ${formulas} formulas, all 8 sections, the abstract, bibliography and ${Object.keys(notes).length} explanations.`);
