import fs from 'node:fs';
import path from 'node:path';
const out=path.resolve('dist/client');
if(!fs.existsSync(path.join(out,'index.html')))throw new Error('The paper was not prerendered. Refusing to produce a release without index.html.');
const prefix=(process.env.PAPER_BASE_PATH||'').replace(/\/$/,'');
if(prefix){
  if(!/^\/[A-Za-z0-9_.\/-]+$/.test(prefix)||prefix.split('/').includes('..'))throw new Error('Invalid Pages prefix');
  // Vinext places path-prefixed assets in that directory. GitHub Pages itself
  // supplies the repository prefix, so the artifact must keep _next at its root.
  const nested=path.join(out,prefix.slice(1),'_next');
  if(fs.existsSync(nested)){
    fs.renameSync(nested,path.join(out,'_next'));
    let dir=path.dirname(nested);
    while(dir!==out&&fs.existsSync(dir)&&fs.readdirSync(dir).length===0){fs.rmdirSync(dir);dir=path.dirname(dir);}
  }
}
fs.writeFileSync(path.join(out,'.nojekyll'),'');
console.log('Prepared static paper'+(prefix?' for '+prefix+'/':' at the root URL'));
