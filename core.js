// Theory of Computation Test 2 — question engine (no DOM; `node core.js` runs self-checks).
// Scope = Week 3–4: regex, regex↔NFA, formal-definition proofs, pumping lemma, CFGs, DFA→CFG.
const rnd=n=>Math.floor(Math.random()*n), pick=a=>a[rnd(a.length)];
const shuffle=a=>{a=a.slice();for(let i=a.length-1;i>0;i--){const j=rnd(i+1);[a[i],a[j]]=[a[j],a[i]]}return a};
const sup=(b,e)=>e===''||e==='1'||e===1?b:e==='0'||e===0?'':b+'<sup>'+e+'</sup>';
const sub=v=>v.replace(/^([A-Za-z])(\d+)$/,'$1<sub>$2</sub>');
function allStrings(sig,n){const out=[''];let layer=[''];for(let k=1;k<=n;k++){layer=layer.flatMap(s=>sig.map(c=>s+c));out.push(...layer)}return out}
// MCQ builder: correct first, shuffled; ans = index of correct
function mcq(q,right,wrongs,steps,extra={}){const opts=shuffle([right,...wrongs.slice(0,3)]);return{type:'mcq',q,opts,ans:opts.indexOf(right),steps,...extra}}
const fact=(q,right,wrongs,why)=>()=>mcq(q,right,wrongs,[why]);

// ───────────── regex engine (course notation: ∪ ∘ * ⁺ ε ∅ Σ, implicit concat) ─────────────
function parseRe(src){const t=[...src.replace(/\s+/g,'')];let i=0;const pk=()=>t[i];
  const U=()=>{let a=C();while(pk()==='∪'){i++;a={t:'u',a,b:C()}}return a};
  const C=()=>{let a=S();while(i<t.length&&pk()!=='∪'&&pk()!==')'){if(pk()==='∘'){i++;continue}a={t:'c',a,b:S()}}return a};
  const S=()=>{let a=A();while(pk()==='*'||pk()==='⁺'){a={t:pk()==='*'?'star':'plus',a};i++}return a};
  const A=()=>{const c=t[i++];if(c===undefined||c===')'||c==='∪'||c==='*'||c==='⁺')throw Error('bad regex '+src);
    if(c==='('){const a=U();if(t[i++]!==')')throw Error('missing ) '+src);return{t:'par',a}}
    return c==='ε'?{t:'eps'}:c==='∅'?{t:'emp'}:c==='Σ'?{t:'sig'}:{t:'sym',v:c}};
  const r=U();if(i!==t.length)throw Error('parse '+src);return r}
function show(n){switch(n.t){case'sym':return n.v;case'eps':return'ε';case'emp':return'∅';case'sig':return'Σ';
  case'par':return'('+show(n.a)+')';case'u':return show(n.a)+' ∪ '+show(n.b);case'c':return show(n.a)+show(n.b);
  case'star':return show(n.a)+'*';case'plus':return show(n.a)+'⁺'}}
const bare=n=>n.t==='par'?show(n.a):show(n);
function toJS(n,sig){const r=x=>toJS(x,sig);switch(n.t){case'sym':return n.v.replace(/[.*+?^${}()|[\]\\]/g,'\\$&');case'eps':return'';case'emp':return'(?!)';
  case'sig':return'['+sig.join('').replace(/[-\]\\^]/g,'\\$&')+']';case'par':return'(?:'+r(n.a)+')';case'u':return'(?:'+r(n.a)+'|'+r(n.b)+')';
  case'c':return r(n.a)+r(n.b);case'star':return'(?:'+r(n.a)+')*';case'plus':return'(?:'+r(n.a)+')+'}}
const reCache={};
function reTest(src,sig){const k=src+'|'+sig;if(!reCache[k]){const R=new RegExp('^(?:'+toJS(parseRe(src),sig)+')$');reCache[k]=w=>R.test(w)}return reCache[k]}
const sameLang=(f,g,sig,n=7)=>allStrings(sig,n).every(w=>f(w)===g(w));
const fmtW=w=>w===''?'ε':w;
// pick one string in / three not in (or reverse)
function memberOpts(test,sig,wantIn,maxLen=5){const all=shuffle(allStrings(sig,maxLen).filter(w=>w.length<=maxLen));
  const yes=all.filter(test),no=all.filter(w=>!test(w));const[A,B]=wantIn?[yes,no]:[no,yes];
  if(!A.length||B.length<3)return null;return{right:A[0],wrongs:B.slice(0,3)}}
// regex mutants that are NOT equivalent (to src or each other)
function mutants(src,sig,k=3){const ok=reTest(src,sig),all=allStrings(sig,6),out=[],seen=new Set([src.replace(/\s/g,'')]);
  for(let tries=0;tries<400&&out.length<k;tries++){const s=[...src.replace(/\s/g,'')],i=rnd(s.length),c=s[i];
    if(c==='*')s[i]=pick(['⁺','']);else if(c==='⁺')s[i]=pick(['*','']);else if(sig.includes(c))s[i]=pick([...sig.filter(x=>x!==c),c+'*']);
    else if(c==='ε')s[i]=pick(sig);else if(c==='Σ')s[i]=pick([...sig,'Σ*','ΣΣ']);else if(c==='∪')s[i]='';else if(c===')')s[i]=pick([')*',')⁺']);else continue;
    if(rnd(4)===0)s.splice(rnd(s.length),1);
    const m=s.join('');if(seen.has(m))continue;seen.add(m);
    try{const f=reTest(m,sig);if(all.some(w=>f(w)!==ok(w))&&out.every(o=>{const g=reTest(o,sig);return all.some(w=>g(w)!==f(w))}))out.push(m)}catch(e){}}
  return out.map(m=>show(parseRe(m)))}

// ───────────── formal-definition proof generator ─────────────
const RULES={1:'1. a ∈ Σ',2:'2. ε',3:'3. ∅',4:'4. R₁ ∪ R₂ (union)',5:'5. R₁ ∘ R₂ (concatenation)',6:'6. R₁* (star)'};
const Rx=s=>'R<sub>'+s+'</sub>';
function proofSteps(src,sig){const ast=parseRe(src),steps=[],seen=new Set();
  const add=(text,rule,res)=>{if(!seen.has(text)){seen.add(text);steps.push({text,rule,res})}};
  const syms=new Set();let hasE=false,hasEmp=false,hasSig=false;
  (function walk(n){if(n.t==='sym')syms.add(n.v);else if(n.t==='eps')hasE=true;else if(n.t==='emp')hasEmp=true;else if(n.t==='sig')hasSig=true;if(n.a)walk(n.a);if(n.b)walk(n.b)})(ast);
  if(hasSig)sig.forEach(c=>syms.add(c));
  const S=sig.filter(c=>syms.has(c));
  if(S.length)add(`${S.join(', ')} ∈ Σ, ∴ ${S.map(Rx).join(', ')}`,1,S);
  if(hasE)add(`ε is the empty string, ∴ ${Rx('ε')}`,2,['ε']);
  if(hasEmp)add(`∅ is the empty language, ∴ ${Rx('∅')}`,3,['∅']);
  if(hasSig)add(`${sig.map(Rx).join(sig.length>2?', ':' and ')} ∴ ${Rx(sig.join(' ∪ '))} = ${Rx('Σ')} (since Σ = ${sig.join(' ∪ ')})`,4,['Σ']);
  (function rec(n){if(n.t==='par')return rec(n.a);if(!n.a)return;
    if(n.t==='star'){rec(n.a);add(`${Rx(bare(n.a))} ∴ ${Rx(show(n))}`,6,[show(n)])}
    if(n.t==='plus'){rec(n.a);const st={t:'star',a:n.a};add(`${Rx(bare(n.a))} ∴ ${Rx(show(st))}`,6,[show(st)]);
      add(`${Rx(bare(n.a))} and ${Rx(show(st))} ∴ ${Rx(show(n))}   (since ${show(n.a)}${show(st)} = ${show(n)})`,5,[show(n)])}
    if(n.t==='u'||n.t==='c'){rec(n.a);rec(n.b);add(`${Rx(bare(n.a))} and ${Rx(bare(n.b))} ∴ ${Rx(show(n))}`,n.t==='u'?4:5,[show(n)])}})(ast);
  return{ast,steps:[{text:'Let R<sub>X</sub> denote the statement “X is regular”.',rule:0},...steps,{text:`∴ L = ${show(ast)} is regular (by the formal definition). ∎`,rule:0}]}}

// ───────────── NFA / DFA ─────────────
function faAccepts(m,w){const E=m.edges.map(([a,b,l])=>[a,b,l.split(',')]);
  const cl=S=>{const st=[...S],out=new Set(S);while(st.length){const q=st.pop();for(const[a,b,l]of E)if(a===q&&l.includes('ε')&&!out.has(b)){out.add(b);st.push(b)}}return out};
  let cur=cl([m.start]);for(const c of w){const nx=new Set();for(const q of cur)for(const[a,b,l]of E)if(a===q&&l.includes(c))nx.add(b);cur=cl(nx)}
  return[...cur].some(q=>m.accept.includes(q))}
function drawFA(m,scale=1){const R=21,P=m.states,ids=Object.keys(P);
  const xs=ids.map(i=>P[i][0]),ys=ids.map(i=>P[i][1]),W=Math.max(...xs)+55,H=Math.max(...ys)+50;
  const g={};m.edges.forEach(([a,b,l,bend])=>{const k=a+'>'+b;g[k]=g[k]||{a,b,l:[],bend};g[k].l.push(l)});
  const lab=s=>s.replace(/^q(\d+)$/,'q<tspan dy="4" font-size="10">$1</tspan>');
  let s=`<svg class="fa" viewBox="0 0 ${W} ${H}" width="${W*scale}" height="${H*scale}"><defs><marker id="ah" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path d="M0,0L10,5L0,10z" fill="currentColor"/></marker></defs>`;
  const st=P[m.start];s+=`<path d="M${st[0]-R-30},${st[1]}L${st[0]-R-1},${st[1]}" stroke="currentColor" marker-end="url(#ah)"/>`;
  for(const e of Object.values(g)){const L=e.l.join(','),[x1,y1]=P[e.a],[x2,y2]=P[e.b];
    if(e.a===e.b){s+=`<path d="M${x1-9},${y1-R+2}C${x1-30},${y1-R-42} ${x1+30},${y1-R-42} ${x1+9},${y1-R+2}" fill="none" stroke="currentColor" marker-end="url(#ah)"/><text x="${x1}" y="${y1-R-36}" text-anchor="middle">${L}</text>`;continue}
    const b=e.bend!==undefined?e.bend:(g[e.b+'>'+e.a]?28:0),dx=x2-x1,dy=y2-y1,len=Math.hypot(dx,dy),nx=-dy/len,ny=dx/len;
    const cx=(x1+x2)/2-nx*b,cy=(y1+y2)/2-ny*b,u=(px,py,qx,qy)=>{const d=Math.hypot(qx-px,qy-py)||1;return[px+(qx-px)/d*R,py+(qy-py)/d*R]};
    const[sx,sy]=u(x1,y1,cx,cy),[ex,ey]=u(x2,y2,cx,cy),mx=.25*sx+.5*cx+.25*ex,my=.25*sy+.5*cy+.25*ey,sg=b>=0?1:-1;
    s+=`<path d="M${sx},${sy}Q${cx},${cy} ${ex},${ey}" fill="none" stroke="currentColor" marker-end="url(#ah)"/><text x="${mx-nx*11*sg}" y="${my-ny*11*sg+4}" text-anchor="middle">${L}</text>`}
  for(const i of ids){const[x,y]=P[i];s+=`<circle cx="${x}" cy="${y}" r="${R}" class="st"/>`+(m.accept.includes(i)?`<circle cx="${x}" cy="${y}" r="${R-4}" fill="none" stroke="currentColor"/>`:'')+`<text x="${x}" y="${y+5}" text-anchor="middle">${lab(i)}</text>`}
  return s+'</svg>'}
const B01=['0','1'];
// regex → NFA bank (positions hand-laid). Self-check verifies L(nfa) = L(re).
const NFAS=[
 {re:'0*1',lvl:1,nfa:{states:{q0:[70,80],q1:[200,80]},start:'q0',accept:['q1'],edges:[['q0','q0','0'],['q0','q1','1']]}},
 {re:'1*0',lvl:1,nfa:{states:{q0:[70,80],q1:[200,80]},start:'q0',accept:['q1'],edges:[['q0','q0','1'],['q0','q1','0']]}},
 {re:'(01)*',lvl:1,nfa:{states:{q0:[70,80],q1:[200,80]},start:'q0',accept:['q0'],edges:[['q0','q1','0'],['q1','q0','1']]}},
 {re:'(0∪1)1*',lvl:1,nfa:{states:{q0:[70,80],q1:[200,80]},start:'q0',accept:['q1'],edges:[['q0','q1','0,1'],['q1','q1','1']]}},
 {re:'(0∪1)*11',lvl:2,nfa:{states:{q0:[70,80],q1:[190,80],q2:[310,80]},start:'q0',accept:['q2'],edges:[['q0','q0','0,1'],['q0','q1','1'],['q1','q2','1']]}},
 {re:'Σ*0Σ*',lvl:2,nfa:{states:{q0:[70,80],q1:[200,80]},start:'q0',accept:['q1'],edges:[['q0','q0','0,1'],['q0','q1','0'],['q1','q1','0,1']]}},
 {re:'0⁺1⁺',lvl:2,nfa:{states:{q0:[70,80],q1:[190,80],q2:[310,80]},start:'q0',accept:['q2'],edges:[['q0','q1','0'],['q1','q1','0'],['q1','q2','1'],['q2','q2','1']]}},
 {re:'ΣΣ',lvl:1,nfa:{states:{q0:[70,80],q1:[190,80],q2:[310,80]},start:'q0',accept:['q2'],edges:[['q0','q1','0,1'],['q1','q2','0,1']]}},
 {re:'(01)*∪1',lvl:2,nfa:{states:{q0:[60,140],q1:[180,80],q2:[310,80],q3:[180,200],q4:[310,200]},start:'q0',accept:['q1','q4'],edges:[['q0','q1','ε'],['q1','q2','0'],['q2','q1','1'],['q0','q3','ε'],['q3','q4','1']]}},
 {re:'(10)*∪0',lvl:2,nfa:{states:{q0:[60,140],q1:[180,80],q2:[310,80],q3:[180,200],q4:[310,200]},start:'q0',accept:['q1','q4'],edges:[['q0','q1','ε'],['q1','q2','1'],['q2','q1','0'],['q0','q3','ε'],['q3','q4','0']]}},
 {re:'0*1∪1*0',lvl:3,nfa:{states:{q0:[60,140],q1:[180,80],q2:[310,80],q3:[180,200],q4:[310,200]},start:'q0',accept:['q2','q4'],edges:[['q0','q1','ε'],['q1','q1','0'],['q1','q2','1'],['q0','q3','ε'],['q3','q3','1'],['q3','q4','0']]}},
 {re:'1(0∪1)*0',lvl:3,nfa:{states:{q0:[70,80],q1:[190,80],q2:[310,80]},start:'q0',accept:['q2'],edges:[['q0','q1','1'],['q1','q1','0,1'],['q1','q2','0']]}},
 {re:'(0∪1)0⁺ ∪ (0∪(0∪1)0⁺)1*',lvl:4,src:'ICA-3A',nfa:{states:{q0:[60,90],q1:[440,90],q2:[190,190],q3:[320,190]},start:'q0',accept:['q1','q3'],edges:[['q0','q1','0',-30],['q0','q2','0,1'],['q2','q3','0'],['q3','q3','0'],['q3','q1','ε'],['q1','q1','1']]}},
 {re:'ε∪(0∪1)(0⁺∪1*∪1⁺0*)',lvl:4,src:'ICA-3B',nfa:{states:{q0:[60,90],q2:[190,90],q1:[440,90],q3:[320,200]},start:'q0',accept:['q0','q1','q3'],edges:[['q0','q2','0,1'],['q2','q1','0'],['q2','q3','ε'],['q3','q3','1'],['q3','q1','1'],['q1','q1','0']]}},
 {re:'1*(1Σ ∪ 1Σ(1∪ε)0* ∪ 0⁺)',lvl:4,src:'ICA-3C',nfa:{states:{q0:[60,170],q1:[190,90],q2:[320,90],q3:[450,170]},start:'q0',accept:['q2','q3'],edges:[['q0','q0','1'],['q0','q1','1'],['q1','q2','0,1'],['q2','q3','1,ε'],['q0','q3','0'],['q3','q3','0']]}},
];
const DFA_M2={name:'M₂ (from the Week 4 notes)',states:{q1:[60,130],q2:[180,80],q3:[300,130],q4:[420,130]},start:'q1',accept:['q4'],
  edges:[['q1','q1','0'],['q1','q2','1'],['q2','q2','1'],['q2','q3','0'],['q3','q1','0',-30],['q3','q4','1'],['q4','q4','0,1']],lang:'{w | w contains the substring 101}'};
function randDFA(){const n=pick([3,3,4]),pos=n===3?[[60,110],[250,110],[155,230]]:[[60,100],[250,100],[250,240],[60,240]];
  const ids=pos.map((_,i)=>'q'+(i+1)),states={};ids.forEach((q,i)=>states[q]=pos[i]);
  const edges=[];ids.forEach(q=>B01.forEach(a=>edges.push([q,pick(ids),a])));
  const acc=shuffle(ids).slice(0,1+rnd(n-1)),M={states,start:'q1',accept:acc.sort(),edges};
  const seen=new Set(['q1']),st=['q1'];while(st.length){const q=st.pop();for(const[a,b]of edges)if(a===q&&!seen.has(b)){seen.add(b);st.push(b)}}
  return seen.size===n&&M.accept.length<n?M:randDFA()} // every state reachable, not all accepting
const delta=(m,q,a)=>m.edges.find(([x,,l])=>x===q&&l.split(',').includes(a))[1];
const Rv=q=>'R'+q.slice(1);
function dfaRules(m){return Object.keys(m.states).map(q=>({v:Rv(q),alts:[...B01.map(a=>a+Rv(delta(m,q,a))),...(m.accept.includes(q)?['ε']:[])]}))}
const altHTML=a=>a.replace(/R(\d+)/g,'R<sub>$1</sub>');
const ruleHTML=r=>`${sub(r.v)} → ${r.alts.map(altHTML).join(' | ')}`;
function dfaDerivation(m,w){let q=m.start,pre='',out=[sub(Rv(q))];for(const c of w){q=delta(m,q,c);pre+=c;out.push(pre+sub(Rv(q)))}out.push(fmtW(pre)+(m.accept.includes(q)?'ε':''));return{steps:out,ok:m.accept.includes(q)}}

// ───────────── CFG engine ─────────────
// G = {S, R:{Var:[rhs,...]}, T?:terminals for display}; rhs tokens: variable = Capital+digits, everything else 1-char terminal, ε/'' = empty
// tokenize against the grammar's variable names (longest match), so "0S1" ≠ "0 S1"
const tok=(r,V)=>{r=r==='ε'?'':r;const vs=Object.keys(V||{}).sort((a,b)=>b.length-a.length),out=[];for(let i=0;i<r.length;){const v=vs.find(v=>r.startsWith(v,i));out.push(v||r[i]);i+=v?v.length:1}return out};
function cfgLang(G,maxLen=7){const res=new Set(),seen=new Set(),q=[[G.S]];let h=0;
  while(h<q.length&&seen.size<300000){const f=q[h++],k=f.findIndex(t=>G.R[t]);if(k<0){res.add(f.join(''));continue}
    for(const r of G.R[f[k]]){const nf=f.slice(0,k).concat(tok(r,G.R),f.slice(k+1));if(nf.filter(t=>!G.R[t]).length>maxLen||nf.length>maxLen+4)continue;
      const key=nf.join(' ');if(!seen.has(key)){seen.add(key);q.push(nf)}}}return res}
function cfgDerive(G,w){const seen=new Map(),q=[[G.S]];seen.set(G.S,null);let h=0;
  while(h<q.length&&seen.size<200000){const f=q[h++],k=f.findIndex(t=>G.R[t]);
    if(k<0){if(f.join('')===w){const path=[];let key=f.join(' ');while(key!==null){path.unshift(key);key=seen.get(key)}return path.map(p=>p.split(' ').filter(Boolean))}continue}
    if(!w.startsWith(f.slice(0,k).join('')))continue;
    for(const r of G.R[f[k]]){const nf=f.slice(0,k).concat(tok(r,G.R),f.slice(k+1));if(nf.filter(t=>!G.R[t]).length>w.length||nf.length>w.length+4)continue;
      const key=nf.join(' ');if(!seen.has(key)){seen.set(key,f.join(' '));q.push(nf)}}}return null}
const formHTML=f=>f.length?f.map(t=>/^[A-Z]\d+$/.test(t)?sub(t):t).join(''):'ε';
const rhsHTML=(r,V)=>r===''||r==='ε'?'ε':tok(r,V).map(t=>V&&V[t]?sub(t):t).join('');
function gHTML(G){const T=G.T||[...new Set(Object.values(G.R).flat().flatMap(r=>tok(r,G.R)).filter(t=>!G.R[t]))].sort().concat('ε');
  return`G = ({${Object.keys(G.R).map(sub).join(', ')}}, {${T.join(', ')}}, R, ${sub(G.S)}) where R:<div class="rules">${Object.entries(G.R).map(([v,a])=>`${sub(v)} → ${a.map(r=>rhsHTML(r,G.R)).join(' | ')}`).join('<br>')}</div>`}
const derivHTML=p=>p.map(formHTML).join(' ⇒ ');
// "length family": L = { u^{k1 n + c1} v^b w^{k3 n + c3} | n ≥ n0 } (sample Q4)
const expr=(k,c)=>{const n=k===0?'':(k===1?'n':k+'n');if(!n)return''+c;return n+(c>0?'+'+c:c<0?'−'+(-c):'')};
const evalE=(k,c,n)=>k*n+c;
function famHTML(F){return`{w ∈ {${F.u}, ${F.v}, ${F.w}}* | w = ${sup(F.u,expr(F.k1,F.c1))}${sup(F.v,''+F.b)}${sup(F.w,expr(F.k3,F.c3))}, n ≥ ${F.n0}}`}
function randFam(){const[u,v,w]=shuffle([['c','a','b'],['x','y','z'],['a','b','c'],['0','1','2']][rnd(4)]);const k1=pick([1,1,1,2]),k3=pick([1,1,2]),c1=pick([-1,0,0,1]),c3=pick([-1,0,1,2]),b=pick([1,2,3]);
  const n0=Math.max(c1<0?1:0,c3<0?1:0,pick([0,1]));return{u,v,w,k1,k3,c1,c3,b,n0}}
const SAMPLE_FAM={u:'c',v:'a',w:'b',k1:1,c1:-1,b:3,k3:1,c3:1,n0:1};
function famLen(F,n){return evalE(F.k1,F.c1,n)+F.b+evalE(F.k3,F.c3,n)}
function famCFG(F){const L0=evalE(F.k1,F.c1,F.n0),R0=evalE(F.k3,F.c3,F.n0),r=(s,k)=>s.repeat(k);
  return{S:'S',R:{S:[r(F.u,L0)+'A'+r(F.w,R0)],A:[r(F.u,F.k1)+'A'+r(F.w,F.k3),r(F.v,F.b)]},T:[F.u,F.v,F.w,'ε']}}
function famPred(F){return s=>{const m=s.match(new RegExp(`^(${F.u}*)(${F.v}+)(${F.w}*)$`));if(!m||m[2].length!==F.b)return false;
  for(let n=F.n0;n<20;n++)if(evalE(F.k1,F.c1,n)===m[1].length&&evalE(F.k3,F.c3,n)===m[3].length)return true;return false}}
function famLenSolve(F,T){const K=F.k1+F.k3,C=F.c1+F.b+F.c3;const n=(T-C)/K;return{K,C,n,ok:Number.isInteger(n)&&n>=F.n0}}
function famLenExplain(F,T){const{K,C,n,ok}=famLenSolve(F,T);const lines=[`|w| = (${expr(F.k1,F.c1)}) + ${F.b} + (${expr(F.k3,F.c3)}) = ${expr(K,C)}`,
  `Set ${expr(K,C)} = ${T} → ${K===1?'':K}n = ${T-C} → n = ${Number.isInteger(n)?n:(T-C)+'/'+K}`];
  lines.push(ok?`n = ${n} is an integer ≥ ${F.n0} ✓ so w = ${sup(F.u,''+evalE(F.k1,F.c1,n))}${sup(F.v,''+F.b)}${sup(F.w,''+evalE(F.k3,F.c3,n))} works.`
    :Number.isInteger(n)?`n = ${n} is below the minimum n ≥ ${F.n0} ✗ — impossible.`:`n isn't an integer ✗ — every string in L has length ${expr(K,C)}, so |w| = ${T} can't be derived.`);return{lines,ok,n}}

// ═════════════ QUESTION GENERATORS: GEN[topic](level 1..4) ═════════════
const TOPICS=[
 {id:'regex',name:'Regular expressions',icon:'🔤'},
 {id:'nfa',name:'Regex ↔ state diagram',icon:'🕸️'},
 {id:'formal',name:'“Show R is regular” proofs',icon:'🧱'},
 {id:'pump',name:'Pumping lemma',icon:'🎈'},
 {id:'cfg',name:'Context-free grammars',icon:'🌳'},
 {id:'dfa2cfg',name:'DFA → CFG',icon:'🔁'},
];
const LEVELS=['','Easy','Medium','Hard','Crazy'];
const RE_EASY=[['0*1','any number of 0s, then one 1'],['(01)*','zero or more copies of 01'],['0∪1','just the single string 0 or 1'],['1*0','any number of 1s, then one 0'],['(0∪1)1','a 0 or 1, then 1'],['0⁺1','one or more 0s, then 1'],['01*','0 followed by any number of 1s'],['(0∪ε)1','1 or 01'],['ΣΣ','every string of length exactly 2']];
const RE_MED=[['(0∪1)*11','strings ending in 11'],['Σ*0Σ*','strings containing at least one 0'],['1*01*','exactly one 0'],['(ΣΣ)*','even length'],['0*1(0∪1)*','contains at least one 1'],['(10)*∪0','(10)ⁿ or the single 0'],['1(01)*∪ε','ε, 1, 101, 10101, …'],['Σ*11Σ*','contains 11'],['(0∪ε)(1∪ε)','ε, 0, 1, 01']];
const RE_DESC=[ // [language description, correct regex]  (distractors = verified non-equivalent mutants)
 ['{w | w starts with 1}','1Σ*'],['{w | w ends with 00}','Σ*00'],['{w | w contains 101}','Σ*101Σ*'],['{w | |w| is odd}','Σ(ΣΣ)*'],
 ['{w | every 1 is immediately followed by a 0}','(0∪10)*'],['{w | w has exactly two 1s}','0*10*10*'],['{w | w starts and ends with the same bit (|w| ≥ 1)}','0∪1∪0Σ*0∪1Σ*1'],
 ['{w | |w| ≤ 2}','(0∪1∪ε)(0∪1∪ε)'],['{w | w does not contain 11}','(0∪10)*(ε∪1)'],['{w | w has at least two 0s}','Σ*0Σ*0Σ*']];
const REGEX_FACTS=[
 fact('Which equals R ∪ ∅?','R',['∅','R ∪ ε','ε'],'Adding the empty language adds no strings: R ∪ ∅ = R (“just like sets”).'),
 fact('Which equals R ∘ ε?','R',['ε','∅','R*'],'Concatenating the empty string changes nothing: R ∘ ε = R.'),
 fact('Which equals R ∘ ∅?','∅',['R','ε','R*'],'Concatenation needs one string from each side; ∅ has none, so R ∘ ∅ = ∅. ({0}∘{} = {})'),
 fact('∅* = ?','ε',['∅','Σ*','undefined'],'Identity 3: ∅* = ε (“weird! like a⁰ = 1”) — star always includes zero copies.'),
 fact('0 ∪ ε describes…','{0, ε}',['{0}','∅','{ε}'],'0 ∪ ε = {0, ε} ≠ 0. ε is a real (empty) string; ∅ is “no strings”.'),
 fact('Order of precedence for regex operators (first → last)?','( ), *, ∘, ∪  — “PKCU”',['∪, ∘, *, ( )','( ), ∘, *, ∪','*, ( ), ∪, ∘'],'Like BEDMAS: Parentheses, Kleene star, Concatenation, Union — the “Pikachu order”.'),
 fact('a⁺ is shorthand for…','aa*',['a*','a ∪ ε','aa'],'a⁺ = a∘a* = a*∘a: one or more a’s.'),
 fact('If Σ = {0,1}, Σ* as a regex is…','(0 ∪ 1)*',['0*1*','(01)*','0* ∪ 1*'],'Σ as a regex = 0 ∪ 1, so Σ* = (0∪1)*: all bit strings.'),
 fact('a⁴ (or a{4}) means…','aaaa',['a ∪ a ∪ a ∪ a','a*','(aaaa)*'],'Exponent = that many concatenated copies.'),
 fact('(a ∪ b)a* describes…','strings starting with one a or b, then any number of a’s',['any string of a’s and b’s','exactly two letters','strings ending in b'],'(a∪b) picks the first letter, a* = zero or more a’s.'),
 fact('Which is NOT a base case of the formal definition of a regular expression?','R₁*',['a for a ∈ Σ','ε','∅'],'Base cases: a ∈ Σ, ε, ∅. Recursive cases: ∪, ∘, *.'),
];
const PREC=[['01*∪1','(0(1*)) ∪ 1',['((01)*) ∪ 1','0(1*∪1)','(0(1*∪1))*']],['0∪1*0','0 ∪ ((1*)0)',['(0∪1)*0','(0∪1*)0','0 ∪ (10)*']],['ab*∪c','(a(b*)) ∪ c',['(ab)* ∪ c','a(b* ∪ c)','a(b∪c)*']],['10∪(ε*00)*','(10) ∪ ((ε*)(00))*',['1(0∪ε*00)*','(10∪ε*00)*','(10) ∪ (ε*)(00)*']]];
const REGEX_EQ=[ // crazy: identities (table 2.1)
 ['(u ∪ v)*',['(u* ∪ v)*','u*(u ∪ v)*','(u*v*)*','u*(vu*)*','(u*v)*u*'],['u*v*','(uv)*','u* ∪ v*']],
 ['(uv)*u',['u(vu)*'],['(uv)*','u(uv)*','(vu)*u']],['u(v ∪ w)',['uv ∪ uw'],['uv ∪ w','u ∪ vw','(uv ∪ w)*']],['u*',['(u*)*'],['u⁺','uu*','u ∪ ε']],
 ['∅*',['ε'],['∅','u*','Σ*']],['ε*',['ε'],['∅','Σ*','ε⁺ ∪ ∅*u']]];
function genRegex(l){
  if(l===1){if(rnd(2))return pick(REGEX_FACTS)();const[re,d]=pick(RE_EASY),f=reTest(re,B01),o=memberOpts(f,B01,true,4);
    return mcq(`Σ = {0,1}. Which string is in L(<b>${re}</b>)?`,fmtW(o.right),o.wrongs.map(fmtW),[`${re} = ${d}.`,...[o.right,...o.wrongs].map(w=>`${fmtW(w)} ${f(w)?'✓ in L':'✗ not in L'}`)])}
  if(l===2){if(rnd(3)===0){const[re,r,w]=pick(PREC);return mcq(`How is <b>${re}</b> parsed (PKCU order)?`,r,w,['Star binds tightest, then concatenation, then union.',`So ${re} = ${r}.`])}
    const[re,d]=pick(RE_MED),f=reTest(re,B01),inn=rnd(2)===0,o=memberOpts(f,B01,inn,5);
    return mcq(`Σ = {0,1}. Which string is ${inn?'':'<u>NOT</u> '}in L(<b>${re}</b>)?`,fmtW(o.right),o.wrongs.map(fmtW),[`${re}: ${d}.`,...[o.right,...o.wrongs].map(w=>`${fmtW(w)} ${f(w)?'✓ in L':'✗ not in L'}`)])}
  if(l===3){const[d,re]=pick(RE_DESC),m=mutants(re,B01,3),R=show(parseRe(re));const f=reTest(re,B01);
    return mcq(`Σ = {0,1}. Which regex describes <b>${d}</b>?`,R,m,[`${R} — matches the description.`,...m.map(x=>{const g=reTest(x,B01),w=allStrings(B01,6).find(s=>g(s)!==f(s));return`${x} ✗ — e.g. ${fmtW(w)} is ${g(w)?'accepted but shouldn’t be':'rejected but should be in L'}`})])}
  if(rnd(2)){const[a,eq,neq]=pick(REGEX_EQ);return mcq(`Which is equivalent to <b>${a}</b> for all regexes u, v, w?`,pick(eq),shuffle(neq),[`Table 2.1 identities: ${a} = ${eq.join(' = ')}.`])}
  const[d,re]=pick(RE_DESC.slice(4)),m=mutants(re,B01,3),R=show(parseRe(re));
  return mcq(`Crazy: which regex is <b>exactly</b> ${d}? (only one is right — check edge cases like ε)`,R,m,[`${R} ✓`,...m.map(x=>{const g=reTest(x,B01),f=reTest(re,B01),w=allStrings(B01,6).find(s=>g(s)!==f(s));return`${x} ✗ on ${fmtW(w)}`})])}

function genNFA(l){
  const pool=NFAS.filter(e=>e.lvl===l||(l===4&&e.lvl>=3)),e=pick(pool.length?pool:NFAS),f=w=>faAccepts(e.nfa,w),sig=B01;
  if(l===1&&rnd(2)){const o=memberOpts(f,sig,true,4);return mcq(`Which string does this NFA accept?${drawFA(e.nfa)}`,fmtW(o.right),o.wrongs.map(fmtW),[`L(N) = ${e.re}.`,...[o.right,...o.wrongs].map(w=>`${fmtW(w)} ${f(w)?'✓ reaches an accept state':'✗ no path ends in an accept state'}`)],{tag:'trace'})}
  if(l<=2&&rnd(2)){const others=shuffle(NFAS.filter(x=>x!==e&&!sameLang(reTest(x.re,sig),f,sig))).slice(0,3);
    return mcq(`Which NFA recognizes <b>${e.re}</b>?`,drawFA(e.nfa,.8),others.map(x=>drawFA(x.nfa,.8)),[`Read each diagram path by path. The right one: every accepted path spells a string of ${e.re}.`,...others.map(x=>`A wrong one recognizes ${x.re} instead.`)],{wide:true})}
  const m=mutants(e.re,sig,3),R=show(parseRe(e.re));
  return mcq(`${e.src?e.src+' style — ':''}Which regex R gives L(N) = R?${drawFA(e.nfa)}`,R,m,[`Split into paths that end in each accept state, write a regex per path, union them.`,`R = ${R}${e.src?' (official solution form)':''}.`,...m.map(x=>{const g=reTest(x,sig),w=allStrings(sig,6).find(s=>g(s)!==f(s));return`${x} ✗ — disagrees on ${fmtW(w)}`})])}

const FORMAL=[['10∪(ε*00)*',B01],['z∪x(y∪x)*',['x','y','z']],['x*∪(zx∪y)*',['x','y','z']],['(2∪10)*∪02',['0','1','2']],['0*1Σ',B01],['(0∪1)⁺(ε∪1)',B01],['01∪1*',B01],['(01)*∪1',B01],['1(0∪ε)*1',B01],['(ab∪c)*a',['a','b','c']]];
const FORMAL_FACTS=[
 fact('A “show R is regular” proof must start with…','the base cases (each symbol a ∈ Σ, ε, ∅ that appears)',['the whole expression','the star operations','an NFA'],'Base cases first: “0, 1 ∈ Σ ∴ R₀, R₁”. Then build up in PKCU order.'),
 fact('Why write “Let R<sub>X</sub> denote ‘X is regular’” first?','to define notation before using it',['to prove the base case','because X is a variable','it is optional decoration'],'The notes: “This is needed, otherwise you are using a notation without establishing what it means.”'),
 fact('Proving a⁺ is regular takes how many steps after R<sub>a</sub>?','2 (a* by star, then a∘a* by concat)',['1 (plus rule)','0','3'],'There is no ⁺ rule: a⁺ = a∘a*, so R_a ∴ R_a* (6), then R_a and R_a* ∴ R_aa* (5).'),
 fact('In what order do you build up the sub-expressions?','inside-out: Parentheses, star, concat, union (PKCU)',['left to right as written','union first','any order'],'Each step may only use pieces already shown regular, so build innermost first.'),
];
function genFormal(l){const[re,sig]=pick(FORMAL),{steps}=proofSteps(re,sig),body=steps.filter(s=>s.rule>0);
  if(l===1){if(rnd(3)===0)return pick(FORMAL_FACTS)();const s=pick(body);return mcq(`Proving L = <b>${re}</b> is regular (Σ = {${sig}}). Which rule justifies:<div class="step">${s.text}</div>`,RULES[s.rule],shuffle(Object.keys(RULES).filter(k=>+k!==s.rule).map(k=>RULES[k])),[`Rule ${RULES[s.rule]}.`,'Rules 1–3 are base cases, 4–6 are recursive (∪, ∘, *).'])}
  const rec=body.filter(s=>s.rule>=4);
  if(l===2){const i=body.indexOf(pick(rec)),s=body[i],later=body.slice(i+1).filter(x=>x.rule>=4);
    const m=s.text.match(/^(.*?) and (.*?) ∴ (.*)$/);
    const wrong=[...new Set([...later.map(x=>x.text),`${Rx(s.res[0])} ∴ ${Rx('('+s.res[0]+')*')}`,`R<sub>${sig[0]}</sub> ∴ ${Rx(s.res[0])}`,...(m?[`${m[1]} ∴ ${m[3]}`,`${m[2]} ∴ ${m[3]}`]:[]),`∴ L = ${re} is regular. ∎`])].filter(x=>x!==s.text);
    const shown=body.slice(0,i).map(x=>x.text).concat(['<b>_____ ?</b>']).join('<br>');
    return mcq(`L = <b>${re}</b>, Σ = {${sig}}. Proof so far:<div class="step">${shown}</div>Which step comes next (PKCU order)?`,s.text,shuffle(wrong).slice(0,3),['Full proof:',...steps.map(x=>x.text)])}
  if(l===3){const bin=rec.filter(s=>s.rule!==6),s=pick(bin.length?bin:rec),m=s.text.match(/^(.*?) and (.*?) ∴ (.*)$/);
    const bad=m?`${m[1]} ∴ ${m[3]}`:s.text.replace(/^(R<sub>.*?<\/sub>) ∴ (.*)$/,'$2 ∴ $1');
    const goods=shuffle(body.filter(x=>x!==s)).slice(0,3).map(x=>x.text);
    return mcq(`Proving <b>${re}</b> regular (Σ = {${sig}}). Which step is <u>invalid</u>?`,bad,goods,[m?'Union/concatenation need BOTH parts already shown regular — this step uses only one.':'Steps can’t run backwards: knowing R* is regular doesn’t give R.','Valid proof:',...steps.map(x=>x.text)])}
  const n=rec.length;return mcq(`Crazy: in the full PKCU proof that <b>${re}</b> is regular (Σ = {${sig}}), how many <u>recursive</u> steps (rules 4–6) are there?`,''+n,[n-1,n+1,n+2].filter(x=>x>0).map(String).concat([''+(n+3)]),['Count one step per ∪, ∘ and * (⁺ counts as two: * then ∘; Σ counts as a union).',...steps.map(x=>x.text)])}

// pumping families
const PUMP=[
 {L:'{0<sup>n</sup>1<sup>n</sup> | n ≥ 0}',s:'0<sup>p</sup>1<sup>p</sup>',len:'2p',X:'0',i:2,pumped:'0<sup>p+k</sup>1<sup>p</sup>',why:'it has more 0s than 1s (p+k ≠ p)',bad:['0<sup>5</sup>1<sup>5</sup>','0<sup>p</sup>1<sup>p+1</sup>','(01)<sup>p</sup>']},
 {L:'{3<sup>n+1</sup>2<sup>2</sup>1<sup>n</sup> | n ≥ 0}',s:'3<sup>p+1</sup>221<sup>p</sup>',len:'2p+3',X:'3',i:0,pumped:'3<sup>p+1−k</sup>221<sup>p</sup>',why:'#3s must equal #1s + 1 = p+1, but it has p+1−k < p+1',bad:['3<sup>4</sup>221<sup>3</sup>','3<sup>p</sup>221<sup>p</sup>','3<sup>p+1</sup>21<sup>p</sup>'],sample:true},
 {L:'{0<sup>2n</sup>1<sup>n</sup> | n ≥ 0}',s:'0<sup>2p</sup>1<sup>p</sup>',len:'3p',X:'0',i:0,pumped:'0<sup>2p−k</sup>1<sup>p</sup>',why:'#0s must be 2·(#1s) = 2p, but it is 2p−k',bad:['0<sup>p</sup>1<sup>p</sup>','0<sup>2p</sup>1<sup>2p</sup>','0<sup>8</sup>1<sup>4</sup>']},
 {L:'{a<sup>n</sup>ba<sup>n</sup> | n ≥ 0}',s:'a<sup>p</sup>ba<sup>p</sup>',len:'2p+1',X:'a',i:2,pumped:'a<sup>p+k</sup>ba<sup>p</sup>',why:'the a-blocks on each side of b are no longer equal',bad:['a<sup>3</sup>ba<sup>3</sup>','a<sup>p</sup>ba<sup>p+1</sup>','a<sup>2p</sup>']},
 {L:'{0<sup>n</sup>1<sup>n+2</sup> | n ≥ 0}',s:'0<sup>p</sup>1<sup>p+2</sup>',len:'2p+2',X:'0',i:2,pumped:'0<sup>p+k</sup>1<sup>p+2</sup>',why:'#1s must be #0s + 2 = p+k+2, but it is p+2',bad:['0<sup>p</sup>1<sup>p</sup>','0<sup>4</sup>1<sup>6</sup>','0<sup>p+2</sup>1<sup>p</sup>']},
 {L:'{x<sup>n</sup>y<sup>n</sup>z<sup>n</sup> | n ≥ 0}',s:'x<sup>p</sup>y<sup>p</sup>z<sup>p</sup>',len:'3p',X:'x',i:2,pumped:'x<sup>p+k</sup>y<sup>p</sup>z<sup>p</sup>',why:'it has more x’s than y’s',bad:['x<sup>3</sup>y<sup>3</sup>z<sup>3</sup>','(xyz)<sup>p</sup>','x<sup>p</sup>y<sup>p</sup>']},
 {L:'{0<sup>n</sup>1<sup>m</sup> | n > m}',s:'0<sup>p+1</sup>1<sup>p</sup>',len:'2p+1',X:'0',i:0,pumped:'0<sup>p+1−k</sup>1<sup>p</sup>',why:'p+1−k ≤ p, so #0s is no longer > #1s (pumping UP would stay in L — you must pump DOWN, i = 0)',bad:['0<sup>p</sup>1<sup>p</sup>','0<sup>2p</sup>1<sup>p</sup>','0<sup>6</sup>1<sup>5</sup>'],crazy:true},
 {L:'{110<sup>n−2</sup>1<sup>n</sup> | n ∈ ℤ⁺, n ≥ 2}',s:'110<sup>p−2</sup>1<sup>p</sup>',len:'2p',X:null,first:'110<sup>p−2</sup>',ica:'ICA-4A',bad:['110<sup>3</sup>1<sup>5</sup>','110<sup>p</sup>1<sup>p</sup>','1<sup>p</sup>0<sup>p−2</sup>11'],
  cases:['If y = 1 or y = 11: xy³z has at least three 1s before the 0s, so xy³z ≠ 110<sup>n−2</sup>1<sup>n</sup>, ∴ xy³z ∉ L.','If y is all 0s: xy³z has too many 0s for its p trailing 1s (#0s ≠ #1s − 2), ∴ xy³z ∉ L.','If y = 1<sup>j</sup>0<sup>k</sup> (j ∈ {1,2}, k ≥ 1): xy³z has extra “10” sections before 1<sup>n</sup>, ∴ xy³z ∉ L.']},
 {L:'{01<sup>n</sup>0<sup>2n</sup> | n ≥ 0}',s:'01<sup>p</sup>0<sup>2p</sup>',len:'3p+1',X:null,first:'01<sup>p−1</sup>',ica:'ICA-4B',bad:['01<sup>3</sup>0<sup>6</sup>','01<sup>p</sup>0<sup>p</sup>','0<sup>2p</sup>1<sup>p</sup>'],
  cases:['If y = 0 or y = 01<sup>j</sup> (y includes the leading 0): xy⁰z begins with 1, ∴ xy⁰z ∉ L.','If y is all 1s: xy⁰z has fewer than p 1s followed by 2p 0s, so the 1:2 ratio is lost, ∴ xy⁰z ∉ L.']},
];
const LENS=['p','p+1','2p','2p+1','2p+2','2p+3','3p','3p+1','p+2'];
const PUMP_FACTS=[
 fact('The pumping lemma for regular languages says: if A is regular then…','∃p such that every s ∈ A with |s| ≥ p splits as xyz with xyⁱz ∈ A ∀i ≥ 0, |y| > 0, |xy| ≤ p',['every string can be pumped','A is finite','∃ one string that can be pumped'],'Read it carefully: if regular ⇒ ALL long strings can be pumped.'),
 fact('Which is the contrapositive used to prove non-regularity?','A can’t be pumped ⇒ A is not regular',['A is not regular ⇒ A can’t be pumped','A can be pumped ⇒ A is regular','A is regular ⇒ A is finite'],'(p→q) ≡ (¬q→¬p). Careful: “can be pumped ⇒ regular” is FALSE (converse).'),
 fact('Which is NOT one of the 3 conditions of the P.L.R.L.?','|z| > 0',['xyⁱz ∈ A for each i ≥ 0','|y| > 0','|xy| ≤ p'],'Conditions: (1) xyⁱz ∈ A ∀i≥0, (2) |y|>0, (3) |xy|≤p. x and z may be empty.'),
 fact('xy⁰z equals…','xz',['xyz','x','ε'],'y⁰ = ε, so xy⁰z = xεz = xz (“pumping down”).'),
 fact('Who chooses p, the pumping length?','the lemma (you must handle ANY p > 0)',['you pick p = 5','p = |s|','p = number of symbols in Σ'],'Write s in terms of p (e.g. 0ᵖ1ᵖ). Plugging in a number like p=5 is only an example, not a proof.'),
 fact('Who chooses the split s = xyz?','the lemma — your argument must cover every possible split',['you choose x, y, z','x is always ε','y is always one symbol'],'That’s why you do cases (or use |xy| ≤ p to force one case).'),
 fact('Step 1 of a pumping proof is…','Assume (for contradiction) that L is regular, so the P.L.R.L. applies',['Assume L is not regular','Draw a DFA for L','Pick i = 2'],'Proof by contradiction: suppose X, always reach a contradiction, conclude X false.'),
 fact('Why is using |xy| ≤ p (“Proof B”) better?','it forces y into the first p symbols — usually one case only',['it makes s shorter','it proves L is regular','it lets you choose y'],'With s = 0ᵖ1ᵖ, the first p symbols are all 0s, so y = 0ᵏ. One case instead of three.'),
];
const REGQ=[['{0<sup>n</sup>1<sup>m</sup> | n, m ≥ 0}',1,'= 0*1* — counts are independent.'],['{0<sup>n</sup>1<sup>n</sup> | n ≥ 0}',0,'needs to remember n — pumping 0ᵖ1ᵖ breaks it.'],
 ['{0<sup>n</sup>1<sup>n</sup> | 0 ≤ n ≤ 100}',1,'finite language ⇒ regular (union of 101 strings).'],['{w | w has an even number of 0s}',1,'2-state DFA tracks parity.'],
 ['{w | #0s = #1s}',0,'pump s = 0ᵖ1ᵖ.'],['{0<sup>2n</sup> | n ≥ 0}',1,'= (00)* — only parity matters.'],['{0<sup>n²</sup> | n ≥ 0}',0,'gaps between squares grow — pumping breaks it.'],
 ['{ww<sup>R</sup> | w ∈ {0,1}*}',0,'even palindromes; pump s = 0ᵖ110ᵖ.'],['{(01)<sup>n</sup> | n ≥ 0}',1,'= (01)*.'],['{0<sup>n</sup>10<sup>n</sup> | n ≥ 0}',0,'pump s = 0ᵖ10ᵖ.'],
 ['{w | w contains 101}',1,'= Σ*101Σ*.'],['{0<sup>n</sup>1<sup>m</sup> | n ≥ m}',0,'pump down s = 0ᵖ1ᵖ.'],['{0<sup>p</sup> | p is prime}',0,'primes aren’t periodic.'],
 ['{w | (#0s − #1s) is divisible by 3}',1,'DFA with 3 states tracks the difference mod 3.'],['{0<sup>n</sup>1<sup>n</sup>} ∪ {0<sup>n</sup>1<sup>m</sup>}',1,'the union is just 0*1* — the hard part is swallowed!']];
function genPump(l){
  if(l===1)return pick(PUMP_FACTS)();
  const F=pick(PUMP.filter(f=>l===4||!f.crazy));
  if(l===2){if(rnd(2))return mcq(`To show L = ${F.L} is non-regular, which s is a good choice?`,F.s,F.bad,[`s = ${F.s} ∈ L and |s| = ${F.len} ≥ p ✓.`,'Must be written with p (not a fixed number), must be in L, and length ≥ p.',`Bonus: its first p symbols ${F.X?`are all ${F.X}s, so y has only one possible form`:`lie inside ${F.first}`}.`]);
    return mcq(`L = ${F.L}, s = ${F.s}. What is |s|?`,F.len,shuffle(LENS.filter(x=>x!==F.len)),[`Add up the block lengths of ${F.s}: |s| = ${F.len} (≥ p ✓).`])}
  if(l===3||F.crazy){if(!F.X)return mcq(`${F.ica}: L = ${F.L}, s = ${F.s}. By |xy| ≤ p, where can y be?`,`anywhere inside ${F.first} — so you need cases`,['only in the 1<sup>p</sup> at the end','y must be all 0s','anywhere in s'],[`|${F.first}| = p, so xy sits inside ${F.first}.`,...F.cases]);
    if(rnd(2))return mcq(`L = ${F.L}, s = ${F.s}. Using |xy| ≤ p and |y| > 0, y must be…`,`${F.X}<sup>k</sup> for some 1 ≤ k ≤ p (only ${F.X}s)`,['a mix of both symbols','only the last symbol','could be anything — need 3 cases'],[`The first p symbols of s are all ${F.X}s and xy lies inside them (|xy| ≤ p).`,'|y| > 0 ⇒ k ≥ 1. One case!']);
    const right=`i = ${F.i}: xy<sup>${F.i}</sup>z = ${F.pumped} ∉ L`,wrong=F.crazy?['i = 2: xy²z ∉ L because it has more 0s','i = 1: xyz ∉ L','i = 0 doesn’t work, pumping only goes up']:[`i = 1: xyz = s ∉ L`,`i = ${F.i}: xy<sup>${F.i}</sup>z = s ∈ L, contradiction`,'no i works — L is regular'];
    return mcq(`L = ${F.L}, s = ${F.s}, y = ${F.X}<sup>k</sup> (1 ≤ k ≤ p). Which pump gives the contradiction?`,right,wrong,[`${right}: ${F.why}.`,'That contradicts condition (1), so L is not regular.'])}
  const isReg=rnd(2)===0,R=REGQ.filter(r=>r[1]===(isReg?1:0)),N=REGQ.filter(r=>r[1]!==(isReg?1:0)),c=pick(R),w=shuffle(N).slice(0,3);
  return mcq(`Crazy: which language is ${isReg?'':'<u>NOT</u> '}regular?`,c[0],w.map(x=>x[0]),[`${c[0]}: ${c[2]}`,...w.map(x=>`${x[0]}: ${x[1]?'regular':'not regular'} — ${x[2]}`)])}

// CFG banks
const G1={S:'A',R:{A:['xAy','AA','ε']},T:['x','y','ε']};
const GRAMMARS=[{name:'G₁ (Week 4 key example)',G:G1},{name:'G₃',G:{S:'A',R:{A:['AB','x'],B:['y','z','ε']},T:['x','y','z','ε']}},
 {name:'G (4.1a)',G:{S:'S',R:{S:['ABA'],A:['1A','ε'],B:['0B','ε']},T:['0','1','ε']}},{name:'G₂',G:{S:'A',R:{A:['A1','A2'],A1:['xA1y','ε'],A2:['0A21','ε']},T:['x','y','0','1','ε']}},
 {name:'G (x²ⁿyⁿ⁺¹)',G:{S:'S',R:{S:['Ay'],A:['xxAy','ε']},T:['x','y','ε']}},{name:'G₄ (expressions)',G:{S:'E',R:{E:['E+T','T'],T:['T×F','F'],F:['(E)','y','z']},T:['y','z','+','×','(',')']}},
 {name:'G₅ (from DFA M₂)',G:{S:'R1',R:{R1:['0R1','1R2'],R2:['1R2','0R3'],R3:['0R1','1R4'],R4:['0R4','1R4','ε']},T:['0','1','ε']}}];
const has=(s,c)=>s.split('').filter(x=>x===c).length;
const CFGQ=[ // [language, sigma, predicate, correct G, wrong Gs]
 ['{0<sup>n</sup>1<sup>n</sup> | n ≥ 0}',B01,w=>/^0*1*$/.test(w)&&has(w,'0')===has(w,'1'),{S:'S',R:{S:['0S1','ε']}},[{S:'S',R:{S:['0S1','01']}},{S:'S',R:{S:['0S','S1','ε']}},{S:'S',R:{S:['01S','ε']}}]],
 ['{x<sup>2n</sup>y<sup>n+1</sup> | n ≥ 0}',['x','y'],w=>{const m=w.match(/^(x*)(y+)$/);return!!m&&m[1].length===2*(m[2].length-1)},{S:'S',R:{S:['Ay'],A:['xxAy','ε']}},[{S:'S',R:{S:['Ay'],A:['xAy','ε']}},{S:'S',R:{S:['Ay'],A:['xxAyy','ε']}},{S:'S',R:{S:['xxSy','ε']}}]],
 ['{1<sup>i</sup>0<sup>j</sup>1<sup>k</sup> | i, j, k ≥ 0} (= 1*0*1*)',B01,w=>/^1*0*1*$/.test(w),{S:'S',R:{S:['ABA'],A:['1A','ε'],B:['0B','ε']}},[{S:'S',R:{S:['AB'],A:['1A','ε'],B:['0B','ε']}},{S:'S',R:{S:['ABA'],A:['1A','ε'],B:['0B','0']}},{S:'S',R:{S:['1S0','ε']}}]],
 ['{w | w starts and ends with the same bit, |w| ≥ 1}',B01,w=>w.length>0&&w[0]===w[w.length-1],{S:'S',R:{S:['0A0','1A1','0','1'],A:['0A','1A','ε']}},[{S:'S',R:{S:['0A0','1A1'],A:['0A','1A','ε']}},{S:'S',R:{S:['0A1','1A0','0','1'],A:['0A','1A','ε']}},{S:'S',R:{S:['0S0','1S1','0','1']}}]],
 ['{w | |w| is odd}',B01,w=>w.length%2===1,{S:'S',R:{S:['0T','1T'],T:['0S','1S','ε']}},[{S:'S',R:{S:['0S','1S','ε']}},{S:'S',R:{S:['00S','01S','10S','11S','ε']}},{S:'S',R:{S:['0T','1T'],T:['0T','1T','ε']}}]],
 ['{w | w contains at least three 1s}',B01,w=>has(w,'1')>=3,{S:'S',R:{S:['A1A1A1A'],A:['0A','1A','ε']}},[{S:'S',R:{S:['A1A1A'],A:['0A','1A','ε']}},{S:'S',R:{S:['1A1A1A'],A:['0A','1A','ε']}},{S:'S',R:{S:['A111A'],A:['0A','1A','ε']}}]],
 ['0* ∘ (0 ∪ 1)',B01,w=>/^0*[01]$/.test(w),{S:'S',R:{S:['A0','A1'],A:['0A','ε']}},[{S:'S',R:{S:['A0','A1'],A:['0A','1A','ε']}},{S:'S',R:{S:['A0','1'],A:['0A','ε']}},{S:'S',R:{S:['0A'],A:['0A','1','ε']}}]],
 ['{1<sup>n</sup>0<sup>n</sup> | n ≥ 0} ∪ (101)*',B01,w=>(/^1*0*$/.test(w)&&has(w,'1')===has(w,'0'))||/^(101)*$/.test(w),{S:'S',R:{S:['A','B'],A:['1A0','ε'],B:['101B','ε']}},[{S:'S',R:{S:['AB'],A:['1A0','ε'],B:['101B','ε']}},{S:'S',R:{S:['A','B'],A:['1A0','ε'],B:['10B','ε']}},{S:'S',R:{S:['A','B'],A:['10A','ε'],B:['101B','ε']}}]],
 ['{w | #0s = #1s}',B01,w=>has(w,'0')===has(w,'1'),{S:'S',R:{S:['0S1S','1S0S','ε']}},[{S:'S',R:{S:['0S1','1S0','ε']}},{S:'S',R:{S:['01S','10S','ε']}},{S:'S',R:{S:['0S1','ε']}}],true],
];
const CFG_FACTS=[
 fact('A CFG is a 4-tuple G = …','(V, Σ, R, S)',['(Q, Σ, δ, q₀, F)','(V, Σ, S)','(V, R, S, F)'],'V variables, Σ terminals, R rules, S start variable.'),
 fact('Which must be true of V and Σ in a CFG?','V ∩ Σ = ∅',['V ⊆ Σ','Σ ⊆ V','V ∪ Σ = ∅'],'Variables and terminals have nothing in common. Also S ∈ V.'),
 fact('Which rule is NOT allowed in a CFG?','xxAy → xAy',['A → xAy','A → ε','A → AA'],'Left side must be a single variable. “xxAy → …” depends on context (“if A has xx before it…”) — not context-free. Same for AB → ….'),
 fact('A → xAy | AA | ε is shorthand for…','three rules: A → xAy, A → AA, A → ε',['one rule','A → xAyAAε','A → x, A → y, A → ε'],'The tall pipe “|” = logical or between alternatives.'),
 fact('L(G) = …','{w ∈ Σ* | S ⇒* w}',['{w | w ∈ V}','all strings over Σ','{S}'],'All terminal strings the grammar produces starting from S.'),
 fact('In a parse tree, the derived string is read from…','the leaves, left to right',['the root','right to left','the internal nodes'],'Leaves left-to-right (ε leaves vanish).'),
 fact('To get L(G) = L₁ ∪ L₂ from grammars for each part, use…','S → A₁ | A₂',['S → A₁A₂','S → A₁* ','S → ε'],'Union = choose one. Concatenation L₁∘L₂ would be S → A₁A₂.'),
 fact('Why can CFGs describe {0ⁿ1ⁿ} while regex can’t?','a rule like A → 0A1 adds matching symbols on both sides at once',['CFGs have more states','CFGs allow ∩','they can’t — it’s not context-free'],'“Quantities depend on each other” → nest them: A → 0A1 | ε.'),
];
function genCFG(l){
  if(l===1)return pick(CFG_FACTS)();
  if(l===2){const{name,G}=pick(GRAMMARS),L=[...cfgLang(G,6)].filter(w=>w.length<=6),T=(G.T||[]).filter(t=>t!=='ε');
    const yes=shuffle(L.filter(w=>w.length>0)),inn=rnd(3)>0||yes.length<3,pool=shuffle(allStrings(T,4).filter(w=>w.length>=1&&!L.includes(w)));
    const right=inn?yes[0]:pool[0],wrongs=inn?pool.slice(0,3):yes.slice(0,3),D=cfgDerive(G,inn?right:wrongs[0]);
    return mcq(`${name}: ${gHTML(G)}Which string is ${inn?'':'<u>NOT</u> '}in L(G)?`,fmtW(right),wrongs.map(fmtW),[D?`Derivation: ${derivHTML(D)}`:'',`${inn?'The others':fmtW(right)} can’t be derived — no sequence of rules from ${sub(G.S)} produces ${inn?'them':'it'}.`].filter(Boolean))}
  if(l===3&&rnd(2)){const F=rnd(3)?randFam():SAMPLE_FAM,base=famLen(F,F.n0),K=F.k1+F.k3,yes=rnd(2)===0;
    let T=base+K*rnd(4);if(!yes)T=K>1&&rnd(2)?T+1+rnd(K-1):base-1-rnd(2);if(T<1)T=base+K;const E=famLenExplain(F,T);
    const right=E.ok?`Yes, n = ${E.n}`:'No — impossible',wr=[...new Set(['No — impossible',...[1,2,3,4,5].map(d=>`Yes, n = ${(E.ok?E.n:Math.max(F.n0,Math.floor((T-base)/K)+F.n0))+d}`)])].filter(x=>x!==right).slice(0,3);
    return mcq(`L = ${famHTML(F)}. Can a string with <b>|w| = ${T}</b> be derived?`,right,wr,E.lines)}
  const pool=CFGQ.filter(x=>l===4||!x[5]),[L,sig,,G,W]=pick(l===4?pool.slice(3):pool);
  return mcq(`${l===4?'Crazy: ':''}Which grammar generates L = ${L}?`,gHTML(G),W.map(gHTML),['Test each against short strings (ε, single symbols, edge cases).',...W.map(g=>{const a=cfgLang(g,6),b=cfgLang(G,6);const d=[...b].find(w=>!a.has(w)),e=[...a].find(w=>!b.has(w));return'✗ '+Object.entries(g.R).map(([v,a])=>`${v} → ${a.map(r=>rhsHTML(r,g.R)).join(' | ')}`).join('; ')+(d!==undefined?` — can’t make ${fmtW(d)}`:` — also makes ${fmtW(e)}`)})],{wide:true})}

const D2C_FACTS=[
 fact('DFA → CFG step 1:','create a variable Rᵢ for each state qᵢ',['create a rule for each symbol','make one variable S','delete the start state'],'One variable per state.'),
 fact('For each transition δ(qᵢ, a) = qⱼ, add the rule…','Rᵢ → aRⱼ',['Rⱼ → aRᵢ','Rᵢ → Rⱼa','Rᵢ → a'],'Read the symbol, then continue from the next state’s variable.'),
 fact('If qᵢ is an accept state, add…','Rᵢ → ε',['Rᵢ → Rᵢ','S → Rᵢ','nothing'],'Stopping in an accept state = allowed to end the string.'),
 fact('The start variable is…','the variable of the DFA’s start state',['always S','the variable of the accept state','R of the last state'],'S = R₀ (or R₁ if states start at q₁).'),
 fact('Deriving a string w of length n in the converted grammar takes how many ⇒ steps?','n + 1',['n','2n','n − 1'],'One step per symbol (Rᵢ → aRⱼ), plus the final Rᵢ → ε.'),
];
function genD2C(l){
  if(l===1)return pick(D2C_FACTS)();
  const M=rnd(3)===0?DFA_M2:randDFA(),rules=dfaRules(M),pic=`<div>${M.name?M.name+':':''}</div>${drawFA(M)}`;
  if(l===2){const r=pick(rules),q='q'+r.v.slice(1),others=Object.keys(M.states).filter(x=>x!==q);
    const swap={...r,alts:[r.alts[0].replace(/R\d+/,r.alts[1].match(/R\d+/)[0]),r.alts[1].replace(/R\d+/,r.alts[0].match(/R\d+/)[0]),...r.alts.slice(2)]};
    const tog={...r,alts:r.alts.includes('ε')?r.alts.filter(a=>a!=='ε'):[...r.alts,'ε']};const rev={...r,alts:r.alts.map(a=>a.replace(/^([01])(R\d+)$/,'$2$1'))};
    const alt={...r,alts:[r.alts[0].replace(/R\d+/,Rv(pick(others))),...r.alts.slice(1)]};
    const alt2={...r,alts:[r.alts[0],r.alts[1].replace(/R\d+/,Rv(pick(others))),...r.alts.slice(2)]},drop={...r,alts:r.alts.filter((_,i)=>i!==1)};
    const opts=[...new Set([swap,tog,alt,rev,alt2,drop].map(ruleHTML))].filter(x=>x!==ruleHTML(r));
    return mcq(`Convert the DFA to a CFG. Which are the rules for ${sub(r.v)}?${pic}`,ruleHTML(r),opts,[`From ${q}: on 0 → ${delta(M,q,'0')}, on 1 → ${delta(M,q,'1')}${M.accept.includes(q)?`, and ${q} accepts so add ε`:', not accepting so no ε'}.`,`${ruleHTML(r)}`])}
  if(l===3){const right=rules.map(ruleHTML).join('<br>'),wr=[];for(let t=0;t<30&&wr.length<3;t++){const rr=rules.map(x=>({...x,alts:[...x.alts]})),k=rnd(rr.length),z=rnd(3);
      if(z===0)rr[k].alts=rr[k].alts.includes('ε')?rr[k].alts.filter(a=>a!=='ε'):[...rr[k].alts,'ε'];else rr[k].alts[z-1]=rr[k].alts[z-1].replace(/R\d+/,Rv(pick(Object.keys(M.states))));
      const h=rr.map(ruleHTML).join('<br>');if(h!==right&&!wr.includes(h))wr.push(h)}
    return mcq(`Which rule set R is the CFG for this DFA (start variable ${sub(Rv(M.start))})?${pic}`,right,wr,['Rᵢ → aRⱼ for each δ(qᵢ,a)=qⱼ; Rᵢ → ε for accept states:',right],{wide:true})}
  const acc=allStrings(B01,5).filter(w=>w.length>=3&&faAccepts(M,w));
  if(acc.length&&rnd(2)){const w=pick(acc),D=dfaDerivation(M,w),X=D.steps[D.steps.length-2];
    const wr=[...new Set([...Object.keys(M.states).map(q=>w+sub(Rv(q))),D.steps[D.steps.length-3],w.slice(0,-1)+X.slice(w.length),w])].filter(x=>x!==X);
    return mcq(`In the CFG from this DFA, the leftmost derivation of <b>${w}</b> — what is the second-to-last line?${pic}`,X,shuffle(wr),['Derivation: '+D.steps.join(' ⇒ '),`${w.length+1} steps: one per symbol + the final ε.`])}
  const o=memberOpts(w=>faAccepts(M,w),B01,true,4);if(!o)return genD2C(3);
  return mcq(`Which string can the converted CFG derive?${pic}`,fmtW(o.right),o.wrongs.map(fmtW),['L(G) = L(M): exactly the strings the DFA accepts.',...[o.right,...o.wrongs].map(w=>`${fmtW(w)}: ${faAccepts(M,w)?'✓ ends in accept state':'✗ ends in non-accept state'}`)])}
const GEN={regex:genRegex,nfa:genNFA,formal:genFormal,pump:genPump,cfg:genCFG,dfa2cfg:genD2C};

// ═════════════ WRITTEN (exam-style, like the sample) ═════════════
function pumpProof(F){if(F.cases)return['Suppose L is regular. Then the P.L.R.L. applies with some pumping length p.',`Let s = ${F.s}, so s ∈ L. |s| = ${F.len} > p.`,'∴ we can split s = xyz such that: (1) xyⁱz ∈ L ∀i ≥ 0, (2) |y| > 0, (3) |xy| ≤ p.',`Using (3), xy is in the ${F.first} part of s, since |${F.first}| = p.`,...F.cases,'All cases contradict (1) of the P.L.R.L.','∴ L is a non-regular language. ∎'];
  return['Assume, for the purpose of finding a contradiction, that L is regular. Then the P.L.R.L. applies with some pumping length p > 0.',`Let s = ${F.s}. Then s ∈ L and |s| = ${F.len} ≥ p.`,'By the P.L.R.L., s = xyz with (1) xyⁱz ∈ L ∀i ≥ 0, (2) |y| > 0, (3) |xy| ≤ p.',`Because |xy| ≤ p, xy lies in the first p symbols of s, which are all ${F.X}s. So y = ${F.X}<sup>k</sup> with 1 ≤ k ≤ p (by (2)). Only one case.`,`Pump with i = ${F.i}: xy<sup>${F.i}</sup>z = ${F.pumped}.`,`But ${F.why}, so xy<sup>${F.i}</sup>z ∉ L. This contradicts (1).`,'∴ L is not regular. ∎']}
const WRITTEN={
 nfa(){const e=pick(NFAS.filter(x=>x.lvl<=3));return{q:`Make a state diagram for L = <b>${e.re}</b> (Σ = {0,1}).`,steps:['Break R into pieces (PKCU): build a small NFA per piece.','Union → new start state with ε-arrows into each piece. Star → loop back to the piece’s start, and make that start accepting (for ε). Concat → chain pieces.','One correct answer:'],ans:drawFA(e.nfa),check:'Test it: does it accept ε? the shortest strings? reject near-misses?'}},
 formal(){const[re,sig]=pick(FORMAL),{steps}=proofSteps(re,sig);return{q:`Σ = {${sig.join(', ')}}. Show that <b>${re}</b> is a regular expression (using the formal definition).`,steps:steps.map(s=>s.text+(s.rule?` <span class="dim">(rule ${s.rule})</span>`:''))}},
 pump(){const F=pick(PUMP.filter(f=>!f.crazy));return{q:`Prove that L = ${F.L} is non-regular.`,steps:pumpProof(F)}},
 cfg(){const F=rnd(3)?randFam():SAMPLE_FAM,G=famCFG(F),K=F.k1+F.k3,C=F.c1+F.b+F.c3,ok=rnd(2),n=F.n0+1+rnd(2),T=ok?K*n+C:K*n+C+(K>1?1:pick([1,-1]))*(K>1?1:1)+(K===1?1:0),E=famLenExplain(F,T);
   const der=E.ok?cfgDerive(G,F.u.repeat(evalE(F.k1,F.c1,E.n))+F.v.repeat(F.b)+F.w.repeat(evalE(F.k3,F.c3,E.n))):null;
   return{q:`(a) Make a CFG for L = ${famHTML(F)}.<br>(b) Make a derivation where the derived string w has <b>|w| = ${T}</b>, or prove that it can’t be derived to that length.`,
    steps:['(a) Matched counts (both depend on n) → nest them with a recursive variable that adds to both sides at once; the fixed middle block is the base case.',
      `Smallest string (n = ${F.n0}): ${sup(F.u,''+evalE(F.k1,F.c1,F.n0))||'ε'}${sup(F.v,''+F.b)}${sup(F.w,''+evalE(F.k3,F.c3,F.n0))} → put that in the S-rule; each +1 to n adds ${sup(F.u,''+F.k1)} on the left and ${sup(F.w,''+F.k3)} on the right.`,gHTML(G),
      ...E.lines.map(x=>'(b) '+x),...(der?['Derivation: '+derivHTML(der)]:[])]}},
 dfa2cfg(){const M=rnd(2)?DFA_M2:randDFA(),R=dfaRules(M),acc=allStrings(B01,5).filter(w=>w.length>=3&&faAccepts(M,w)),w=acc.length?pick(acc):null;
   return{q:`Convert the following DFA into a CFG${w?`, then derive <b>${w}</b>`:''}.${drawFA(M)}`,steps:['① a variable Rᵢ for each state qᵢ. ② S = R of the start state. ③ Rᵢ → aRⱼ for each δ(qᵢ,a)=qⱼ, and Rᵢ → ε if qᵢ accepts.',
     `G = ({${R.map(r=>sub(r.v)).join(', ')}}, {0, 1, ε}, R, ${sub(Rv(M.start))}) where R:<div class="rules">${R.map(ruleHTML).join('<br>')}</div>`,...(w?['Derivation: '+dfaDerivation(M,w).steps.join(' ⇒ ')]:[])]}},
 regex(){const[d,re]=pick(RE_DESC);return{q:`Σ = {0,1}. Give a regular expression R for ${d}, and list 3 strings in L(R) and 2 not in it.`,steps:[`One answer: R = ${show(parseRe(re))}`,`In: ${allStrings(B01,4).filter(reTest(re,B01)).slice(0,4).map(fmtW).join(', ')} · Out: ${allStrings(B01,3).filter(w=>!reTest(re,B01)(w)).slice(0,3).map(fmtW).join(', ')}`]}},
};
const BONUS=[
 ()=>({q:'BONUS: Prove that L = {0<sup>n</sup>1<sup>m</sup> | n > m} is non-regular. (Careful which way you pump!)',steps:pumpProof(PUMP.find(f=>f.crazy))}),
 ()=>({q:'BONUS: Give a CFG for {w ∈ {0,1}* | w has the same number of 0s and 1s}, and derive 0110.',steps:['Any balanced string is ε, or starts with 0 and its matching 1 splits it into two balanced parts (same with 1…0).',gHTML({S:'S',R:{S:['0S1S','1S0S','ε']}}),'Derivation: '+derivHTML(cfgDerive({S:'S',R:{S:['0S1S','1S0S','ε']}},'0110'))]}),
 ()=>({q:'BONUS: Is {0<sup>n</sup>1<sup>n</sup> | 0 ≤ n ≤ 1000} regular? Justify.',steps:['Yes! It’s finite (1001 strings).','Every finite language is regular: union of the strings as a regex, e.g. ε ∪ 01 ∪ 0011 ∪ … — the pumping lemma never contradicts it (pick p larger than the longest string).']}),
 ()=>({q:'BONUS: Give a CFG for even-length palindromes over {a,b} and prove the language isn’t regular.',steps:[gHTML({S:'S',R:{S:['aSa','bSb','ε']}}),'Non-regular: assume regular, s = a<sup>p</sup>bba<sup>p</sup> ∈ L, |s| = 2p+2 ≥ p.','|xy| ≤ p ⇒ y = a<sup>k</sup>, k ≥ 1. xy²z = a<sup>p+k</sup>bba<sup>p</sup> isn’t a palindrome ⇒ ∉ L, contradiction. ∎']}),
];
const WRITTEN_FOR={regex:'regex',nfa:'nfa',formal:'formal',pump:'pump',cfg:'cfg',dfa2cfg:'dfa2cfg'};

if(typeof module!=='undefined'){ // ── self-checks: node core.js
  const assert=require('assert');
  for(const e of NFAS)assert(sameLang(reTest(e.re,B01),w=>faAccepts(e.nfa,w),B01,8),'NFA≠regex: '+e.re);
  for(const[d,re]of RE_DESC)reTest(re,B01);
  assert(reTest('10∪(ε*00)*',B01)('0000')&&reTest('10∪(ε*00)*',B01)('10')&&!reTest('10∪(ε*00)*',B01)('100'));
  const D=t=>[...t].sort().join(',');
  for(const[L,sig,pred,G,W]of CFGQ){const want=new Set(allStrings(sig,6).filter(pred)),got=cfgLang(G,6);
    assert.deepStrictEqual(D(got),D(want),'CFG wrong for '+L);for(const g of W)assert.notDeepStrictEqual(D(cfgLang(g,6)),D(want),'distractor correct for '+L)}
  for(let t=0;t<60;t++){const F=t?randFam():SAMPLE_FAM,G=famCFG(F),sig=[F.u,F.v,F.w],want=allStrings(sig,7).filter(famPred(F));
    assert.deepStrictEqual(D(cfgLang(G,7)),D(want),'family CFG '+JSON.stringify(F))}
  assert(famLenExplain(SAMPLE_FAM,9).ok&&famLenExplain(SAMPLE_FAM,9).n===3&&!famLenExplain(SAMPLE_FAM,10).ok);
  const G5=GRAMMARS[6].G;for(const w of allStrings(B01,6))assert.strictEqual(cfgLang(G5,6).has(w),faAccepts(DFA_M2,w),'G5 '+w);
  for(let t=0;t<20;t++){const M=randDFA(),R=dfaRules(M),G={S:Rv(M.start),R:Object.fromEntries(R.map(r=>[r.v,r.alts]))};const L=cfgLang(G,5);for(const w of allStrings(B01,5))assert.strictEqual(L.has(w),faAccepts(M,w))}
  const p=proofSteps('(0∪1)⁺(ε∪1)',B01).steps.map(s=>s.text).join('\n');assert(p.includes('R<sub>(0 ∪ 1)*</sub>'),p);
  let n=0;for(const t of TOPICS)for(let l=1;l<=4;l++)for(let k=0;k<150;k++){const q=GEN[t.id](l);assert(q.opts.length===4&&q.ans>=0&&new Set(q.opts).size===4,`${t.id} L${l}: ${q.q}\n${q.opts}`);n++}
  for(const k in WRITTEN)for(let i=0;i<40;i++)assert(WRITTEN[k]().steps.length);BONUS.forEach(b=>assert(b().steps.length));
  console.log('ok —',n,'MCQs generated, all banks verified');
}
