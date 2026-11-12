// Durak rules engine for 2–6 players. Pure state + actions; the UI and AI only call these methods.
// Modes: 'podkidnoy' (throw-in) and 'perevodnoy' (transfer). Decks: 24 (9..A), 36 (6..A), 52 (2..A), 54 (2..A + two jokers).
// Everyone except the defender may throw in (or only the attacker and the defender's other neighbour with rules.neighbors).
// First bout is limited to 5 cards, later ones to 6 (rules.noLimit: only by the defender's hand).
// rules.show: in the transfer game a trump of the same rank may be shown instead of laid to pass the attack on.
const SUITS=['s','c','h','d'];
const R36=['6','7','8','9','10','В','Д','К','Т'],R52=['2','3','4','5'].concat(R36),R24=R36.slice(3);
const RANKS=R36; // default order, kept for code that only cares about names
const isJ=c=>c.r==='J';

function makeRng(seed){let s=(seed>>>0)||1;return ()=>{s^=s<<13;s>>>=0;s^=s>>>17;s^=s<<5;s>>>=0;return s/4294967296;};}

function Game(opts){
  opts=opts||{};
  this.mode=opts.mode||'podkidnoy';
  this.deckSize=[24,36,52,54].includes(opts.deck)?opts.deck:36;
  this.rules=Object.assign({neighbors:false,show:false,noLimit:false,cheat:false},opts.rules||{});
  this.teams=opts.teams||null; // pair game: team id per seat, e.g. [0,1,0,1]
  this.n=Math.max(2,Math.min(opts.players||2,this.deckSize===24?4:this.deckSize===36?5:6));
  this.rng=opts.rng||Math.random;
  this.ranks=this.deckSize===24?R24:this.deckSize===36?R36:R52;
  this.events=[];
  const deck=[];for(const s of SUITS)for(const r of this.ranks)deck.push({r,s,id:r+s});
  if(this.deckSize===54){deck.push({r:'J',s:'b',id:'Jb'},{r:'J',s:'r',id:'Jr'});}
  for(let i=deck.length-1;i>0;i--){const j=Math.floor(this.rng()*(i+1));[deck[i],deck[j]]=[deck[j],deck[i]];}
  // the face-up bottom card sets the trump suit, so it must not be a joker
  if(isJ(deck[0])){const k=deck.findIndex(c=>!isJ(c));[deck[0],deck[k]]=[deck[k],deck[0]];}
  this.deck=deck;this.trumpCard=deck[0];this.trump=deck[0].s;
  this.hands=[];this.known=[];this.played=[];for(let p=0;p<this.n;p++){this.hands.push([]);this.known.push(new Set());this.played.push([]);}
  this.table=[];this.discard=[];this.out=[];this.over=false;this.fool=-1;this.pogony=0;this.firstBout=true;this.bouts=0;
  for(let i=0;i<6;i++)for(let p=0;p<this.n;p++)this.hands[p].push(this.deck.pop());
  // lowest trump leads
  let best=-1,bv=99;for(let p=0;p<this.n;p++)for(const c of this.hands[p])if(c.s===this.trump&&this.rk(c)<bv){bv=this.rk(c);best=p;}
  this.att=opts.first!=null?opts.first:(best>=0?best:Math.floor(this.rng()*this.n));
  this.def=this.nextDef(this.att);
  this.startBout();
}
const G=Game.prototype;
G.rk=function(c){return isJ(c)?this.ranks.length+(c.s==='r'?1:0):this.ranks.indexOf(c.r);};
G.isTrump=function(c){return c.s===this.trump;};
G.beats=function(d,a){
  if(isJ(d))return !isJ(a)||(d.s==='r'&&a.s==='b');
  if(isJ(a))return false;
  return (d.s===a.s&&this.rk(d)>this.rk(a))||(d.s===this.trump&&a.s!==this.trump);};
G.active=function(p){return this.out.indexOf(p)<0;};
G.mate=function(p,q){return !!this.teams&&p!==q&&this.teams[p]===this.teams[q];};
// who defends against p: the next player, skipping p's partner in the pair game while an opponent is left
G.nextDef=function(p){let q=this.nextActive(p);if(this.teams&&this.mate(p,q)){const r=this.nextActive(q);if(r!==p&&!this.mate(p,r))q=r;}return q;};
G.teamsLeft=function(){const s=new Set();for(let p=0;p<this.n;p++)if(this.active(p))s.add(this.teams[p]);return s.size;};
G.activeCount=function(){return this.n-this.out.length;};
G.nextActive=function(p){for(let k=1;k<=this.n;k++){const q=(p+k)%this.n;if(this.active(q))return q;}return p;};
G.throwers=function(){const r=[];
  if(this.rules.neighbors&&this.activeCount()>2){const nb=this.nextActive(this.def);r.push(this.att);if(nb!==this.att&&nb!==this.def)r.push(nb);return r;}
  for(let k=0;k<this.n;k++){const q=(this.att+k)%this.n;if(q!==this.def&&this.active(q)&&!this.mate(q,this.def))r.push(q);}return r;};
G.limitBase=function(){return this.rules.noLimit?99:this.firstBout?5:6;};
G.ranksOnTable=function(){const s=new Set();for(const p of this.table){s.add(p.a.r);if(p.d)s.add(p.d.r);}return s;};
G.undefended=function(){return this.table.filter(p=>!p.d);};
G.startBout=function(){
  this.table=[];this.taking=false;this.passed=new Set();this.shown=new Set();
  for(let p=0;p<this.n;p++)this.played[p]=[];
  this.limit=Math.min(this.limitBase(),this.hands[this.def].length);
  this.events.push({t:'bout',att:this.att,def:this.def});
};
G.has=function(p,c){return this.hands[p].indexOf(c)>=0;};
G.removeFrom=function(p,c){const h=this.hands[p];h.splice(h.indexOf(c),1);this.known[p].delete(c.id);this.played[p].push(c);};

// ---------- legality ----------
G.canAttack=function(p,c){
  if(this.over||p===this.def||!this.active(p)||!this.has(p,c))return false;
  if(this.table.length===0)return p===this.att;
  if(this.table.length>=this.limit)return false;
  if(!this.taking&&this.undefended().length>=this.hands[this.def].length)return false;
  return this.ranksOnTable().has(c.r);
};
G.canDefend=function(p,c,i){
  if(this.over||p!==this.def||this.taking||!this.has(p,c))return false;
  const pr=this.table[i];return !!pr&&!pr.d&&this.beats(c,pr.a);
};
G.transferTarget=function(){return this.nextDef(this.def);};
G.canTransfer=function(p,c){
  if(this.over||this.mode!=='perevodnoy'||p!==this.def||this.taking||!this.has(p,c))return false;
  if(!this.table.length||this.table.some(x=>x.d))return false;
  if(this.table.some(x=>x.a.r!==c.r))return false;
  const n=this.table.length+1;
  return n<=this.limitBase()&&this.hands[this.transferTarget()].length>=n;
};
// show a trump of the table's rank instead of laying a card: the attack moves on, the trump stays in hand
G.canShow=function(p,c){
  if(this.over||this.mode!=='perevodnoy'||!this.rules.show||p!==this.def||this.taking||!this.has(p,c)||!this.isTrump(c)||this.shown.has(c.id))return false;
  if(!this.table.length||this.table.some(x=>x.d||x.a.r!==c.r))return false;
  return this.table.length<=this.limitBase()&&this.hands[this.transferTarget()].length>=this.table.length;
};
G.canTake=function(p){return !this.over&&p===this.def&&!this.taking&&this.undefended().length>0;};
G.canDone=function(p){ // a thrower says "бито" (or "хватит" after a take)
  if(this.over||p===this.def||!this.active(p)||!this.table.length)return false;
  return this.taking||this.undefended().length===0;
};

// ---------- actions (return true when applied) ----------
G.attack=function(p,c){if(!this.canAttack(p,c))return false;this.removeFrom(p,c);this.table.push({a:c});this.passed.clear();this.events.push({t:'attack',p,c});this.settle();return true;};
G.defend=function(p,c,i){if(i==null)i=this.table.findIndex(x=>!x.d&&this.beats(c,x.a));if(!this.canDefend(p,c,i))return false;
  this.removeFrom(p,c);this.table[i].d=c;this.events.push({t:'defend',p,c,i});this.settle();return true;};
G.transfer=function(p,c){if(!this.canTransfer(p,c))return false;const nd=this.transferTarget();this.removeFrom(p,c);this.table.push({a:c});
  this.att=p;this.def=nd;this.limit=Math.min(this.limitBase(),this.hands[nd].length);this.passed.clear();
  this.events.push({t:'transfer',p,c,to:nd});return true;};
G.show=function(p,c){if(!this.canShow(p,c))return false;const nd=this.transferTarget();this.shown.add(c.id);this.known[p].add(c.id);
  this.att=p;this.def=nd;this.limit=Math.min(this.limitBase(),this.hands[nd].length);this.passed.clear();
  this.events.push({t:'show',p,c,to:nd});return true;};
G.cheatDefend=function(p,c,i){if(!this.rules.cheat||this.over||p!==this.def||this.taking||!this.has(p,c))return false;const pr=this.table[i];if(!pr||pr.d)return false;
  this.removeFrom(p,c);pr.d=c;pr.cheat=p;this.events.push({t:'defend',p,c,i,cheat:true});this.settle();return true;};
G.cheatAttack=function(p,c){if(!this.rules.cheat||this.over||p===this.def||!this.active(p)||!this.has(p,c)||!this.table.length||this.table.length>=this.limit)return false;
  if(!this.taking&&this.undefended().length>=this.hands[this.def].length)return false;
  this.removeFrom(p,c);this.table.push({a:c,cheat:p});this.passed.clear();this.events.push({t:'attack',p,c,cheat:true});this.settle();return true;};
G.cheater=function(){const pr=this.table.find(x=>x.cheat!=null);return pr?pr.cheat:-1;};
// someone cried "caught!": the cheater, or the wrong accuser, picks up the table and the bout ends
G.accuse=function(p){if(this.over||!this.table.length)return false;const ch=this.cheater(),loser=ch>=0?ch:p;
  this.events.push({t:'accuse',p,caught:ch>=0,loser});this.penalty(loser);return true;};
G.penalty=function(p){const cards=this.table.flatMap(x=>x.d?[x.a,x.d]:[x.a]),pairs=this.table.map(x=>({a:x.a,d:x.d}));
  this.hands[p].push(...cards);cards.forEach(c=>this.known[p].add(c.id));this.events.push({t:'took',p,cards,pairs,att:this.att,penalty:true});
  this.table=[];this.firstBout=false;this.bouts++;
  const order=[];for(let k=0;k<this.n;k++){const q=(this.att+k)%this.n;if(this.active(q))order.push(q);}
  for(const q of order){while(this.hands[q].length<6&&this.deck.length){const c=this.deck.pop();this.hands[q].push(c);if(c===this.trumpCard)this.known[q].add(c.id);this.events.push({t:'draw',p:q,c});}}
  if(!this.deck.length)for(const q of order)if(this.hands[q].length===0&&this.active(q)){this.out.push(q);this.events.push({t:'out',p:q,place:this.out.length});}
  if(this.activeCount()<=1||(this.teams&&this.teamsLeft()<=1)){this.over=true;const left=[...Array(this.n).keys()].filter(q=>this.active(q));
    this.fool=!left.length?-1:left.sort((a,b)=>this.hands[b].length-this.hands[a].length)[0];this.loserTeam=this.teams&&left.length?this.teams[left[0]]:null;this.lastPlayed=this.played.map(x=>x.slice());this.events.push({t:'over',fool:this.fool,pogony:0});return;}
  this.lastPlayed=this.played.map(x=>x.slice());
  this.att=this.nextActive(p);this.def=this.nextDef(this.att);this.startBout();};
G.take=function(p){if(!this.canTake(p))return false;this.taking=true;this.passed.clear();this.events.push({t:'take',p});this.settle();return true;};
G.done=function(p){if(!this.canDone(p))return false;this.passed.add(p);this.events.push({t:'pass',p});this.settle();return true;};
// after every action: skip throwers who have nothing to add; end the bout when nobody can
G.settle=function(){
  if(this.over||!this.table.length)return;
  if(!this.taking&&this.undefended().length>0)return;
  if(!this.taking&&this.hands[this.def].length===0)return this.endBout(false);
  for(const q of this.throwers()){if(this.passed.has(q))continue;if(this.hands[q].some(c=>this.canAttack(q,c)))return;this.passed.add(q);}
  this.endBout(this.taking);
};
G.endBout=function(took){
  const cards=this.table.flatMap(x=>x.d?[x.a,x.d]:[x.a]),pairs=this.table.map(x=>({a:x.a,d:x.d}));
  const lastPlayed=this.played.map(x=>x.slice());
  if(took){this.hands[this.def].push(...cards);cards.forEach(c=>this.known[this.def].add(c.id));this.events.push({t:'took',p:this.def,cards,pairs,att:this.att});}
  else{this.discard.push(...cards);this.events.push({t:'bito',cards,pairs,att:this.att,def:this.def});}
  this.table=[];this.firstBout=false;this.bouts++;
  // refill: main attacker, then the other throwers clockwise, the defender last
  const order=this.throwers().concat(this.active(this.def)?[this.def]:[]);
  // players who could not throw in this bout (partners, non-neighbours) refill last
  for(let k=0;k<this.n;k++){const q=(this.att+k)%this.n;if(this.active(q)&&order.indexOf(q)<0)order.push(q);}
  for(const p of order){while(this.hands[p].length<6&&this.deck.length){const c=this.deck.pop();this.hands[p].push(c);if(c===this.trumpCard)this.known[p].add(c.id);this.events.push({t:'draw',p,c});}}
  // players with no cards once the deck is empty are out of the game
  const goneNow=[];
  if(!this.deck.length)for(const p of order)if(this.hands[p].length===0&&this.active(p)){this.out.push(p);goneNow.push(p);this.events.push({t:'out',p,place:this.out.length});}
  if(this.activeCount()<=1||(this.teams&&this.teamsLeft()<=1)){
    this.over=true;const left=[...Array(this.n).keys()].filter(p=>this.active(p));
    // in the pair game the team still holding cards loses; its member with the most cards is the fool
    this.fool=!left.length?-1:left.length===1?left[0]:left.sort((a,b)=>this.hands[b].length-this.hands[a].length)[0];
    this.loserTeam=this.teams&&left.length?this.teams[left[0]]:null;
    if(this.fool>=0){let six=0;for(const p of goneNow)six+=lastPlayed[p].filter(c=>c.r==='6').length;this.pogony=Math.min(2,six);}
    this.lastPlayed=lastPlayed;this.events.push({t:'over',fool:this.fool,pogony:this.pogony});return;
  }
  this.lastPlayed=lastPlayed;
  const prevDef=this.def;
  this.att=took?this.nextActive(prevDef):(this.active(prevDef)?prevDef:this.nextActive(prevDef));
  this.def=this.nextDef(this.att);
  this.startBout();
};
// whose input the game waits for
G.toMove=function(){if(this.over)return -1;
  if(!this.table.length)return this.att;
  if(!this.taking&&this.undefended().length>0)return this.def;
  for(const q of this.throwers())if(!this.passed.has(q))return q;
  return this.att;};
// every legal action for player p when it is p's turn (used by AI and tests)
G.legal=function(p){const out=[];if(this.over||p!==this.toMove())return out;const h=this.hands[p];
  if(p===this.def&&!this.taking&&this.undefended().length){
    for(const c of h){if(this.canTransfer(p,c))out.push({t:'transfer',c});if(this.canShow(p,c))out.push({t:'show',c});this.table.forEach((x,i)=>{if(this.canDefend(p,c,i))out.push({t:'defend',c,i});});}
    out.push({t:'take'});return out;}
  for(const c of h)if(this.canAttack(p,c))out.push({t:'attack',c});
  if(this.canDone(p))out.push({t:'done'});
  return out;};
G.apply=function(p,m){if(!m)return false;switch(m.t){case'attack':return this.attack(p,m.c);case'defend':return this.defend(p,m.c,m.i);case'transfer':return this.transfer(p,m.c);case'show':return this.show(p,m.c);case'take':return this.take(p);case'done':return this.done(p);}return false;};
G.count=function(){return this.deck.length+this.hands.reduce((a,h)=>a+h.length,0)+this.discard.length+this.table.reduce((a,x)=>a+1+(x.d?1:0),0);};
// cheap copy for AI look-ahead (no events, shared card objects)
G.clone=function(){const g=Object.create(Game.prototype);
  for(const k of ['mode','deckSize','rules','teams','loserTeam','n','rng','ranks','trumpCard','trump','over','fool','pogony','firstBout','bouts','att','def','limit','taking','lastPlayed'])g[k]=this[k];
  g.events=[];g.deck=this.deck.slice();g.hands=this.hands.map(h=>h.slice());g.table=this.table.map(x=>x.cheat!=null?{a:x.a,d:x.d,cheat:x.cheat}:{a:x.a,d:x.d});g.discard=this.discard.slice();
  g.known=this.known.map(s=>new Set(s));g.played=this.played.map(x=>x.slice());g.out=this.out.slice();g.passed=new Set(this.passed);g.shown=new Set(this.shown||[]);return g;};
G.key=function(){const h=x=>x.map(c=>c.id).sort().join(',');return this.att+'|'+this.def+'|'+this.taking+'|'+[...this.passed].join('')+'|'+this.hands.map(h).join('|')+'|'+this.table.map(x=>x.a.id+(x.d?'/'+x.d.id:'')).join(';')+'|'+this.limit+'|'+this.out.join('')+'|'+[...(this.shown||[])].join('');};


;
// Opponent AI for any seat. Personas are style knobs over one shared player:
//  - a quick heuristic player (all levels; also the "imagination" of the strong ones),
//  - strong levels think ahead: they deal the unseen cards in many plausible ways, play each candidate
//    move a couple of bouts forward and pick the move that does best on average (Monte Carlo search),
//  - at the very end (deck empty, two players) they solve the position exactly.
const STYLES={
  easy:   {multi:.2,greed:1.45,tossMax:3,tossTrumpLate:false,noise:.28,memory:false,transferBias:.35,leadTrumpPenalty:10},
  sly:    {multi:.85,greed:.85,tossMax:6,tossTrumpLate:true,noise:.1,memory:false,transferBias:.95,leadTrumpPenalty:8},
  bold:   {multi:.6,greed:.7,tossMax:5,tossTrumpLate:true,noise:.08,memory:false,transferBias:.8,leadTrumpPenalty:7},
  shrewd: {multi:.5,greed:1.0,tossMax:4,tossTrumpLate:true,noise:0,memory:true,transferBias:1,leadTrumpPenalty:12,searchBudget:6000,mc:{ms:45,horizon:2}},
  master: {multi:.55,greed:.95,tossMax:4,tossTrumpLate:true,noise:0,memory:true,transferBias:1,leadTrumpPenalty:12,searchBudget:20000,mc:{ms:110,horizon:3}},
};
const PERSONAS={kuzmich:STYLES.easy,nura:STYLES.sly,kupets:STYLES.shrewd};
const ROLL=Object.assign({},STYLES.bold,{noise:0,memory:false}); // how the strong bots imagine everyone plays
const now=()=>(typeof performance!=='undefined'?performance.now():Date.now());

// perfect-information endgame search (deck empty, two players left): +1 win, -1 loss, 0 draw for player p
function solveEnd(g,p,budget){
  const memo=new Map();let nodes=0;
  function rec(st){
    if(st.over)return st.fool===-1?0:(st.fool===p?-1:1);
    if(++nodes>budget)throw 0;
    const k=st.key();if(memo.has(k))return memo.get(k);
    const q=st.toMove();const L=st.legal(q);let best=q===p?-2:2;
    for(const m of L){const c=st.clone();c.apply(q,m);const v=rec(c);
      if(q===p){if(v>best)best=v;if(best===1)break;}else{if(v<best)best=v;if(best===-1)break;}}
    memo.set(k,best);return best;}
  try{const L=g.legal(p);let best=null,bv=-2;
    for(const m of L){const c=g.clone();c.apply(p,m);const v=rec(c);if(v>bv){bv=v;best=m;}if(bv===1)break;}
    return {move:best,value:bv};}catch(e){return null;}
}

function aiMove(g,p,persona,rng,opts){
  rng=rng||Math.random;const P=persona||STYLES.easy;
  const L=g.legal(p);if(!L.length)return null;if(L.length===1)return L[0];
  const late=g.deck.length===0,two=g.activeCount()===2;
  if(P.memory&&late&&two&&g.hands.reduce((a,h)=>a+h.length,0)<=14){
    const r=solveEnd(g,p,P.searchBudget||6000);if(r&&r.move&&r.value>=0)return r.move;}
  if(P.mc&&!(opts&&opts.fast)){const m=mcMove(g,p,P,rng,L);if(m)return m;}
  return heuristicMove(g,p,P,rng,L);
}

/* ---------------- quick heuristic player ---------------- */
function heuristicMove(g,p,P,rng,L){
  L=L||g.legal(p);if(!L.length)return null;
  const late=g.deck.length===0,two=g.activeCount()===2;
  const T=c=>g.isTrump(c),J=c=>c.r==='J';
  const top=g.ranks.length-1,rn=c=>J(c)?9:g.rk(c)*8/top;      // rank on a 0..8 scale for any deck
  const val=c=>J(c)?30:rn(c)+(T(c)?9:0);
  // what is known of the defender's hand (cards they picked up are public), or the whole of it at the end
  let oppHand=null;
  if(P.memory){const opp=p===g.def?null:g.def;
    if(late&&two){const out=new Set([...g.hands[p],...g.discard,...g.table.flatMap(x=>x.d?[x.a,x.d]:[x.a])].map(c=>c.id));
      oppHand=[];for(const s of SUITS)for(const r of g.ranks){const id=r+s;if(!out.has(id))oppHand.push({r,s,id});}
      if(g.deckSize===54)for(const s of ['b','r'])if(!out.has('J'+s))oppHand.push({r:'J',s,id:'J'+s});}
    else if(opp!=null)oppHand=g.hands[opp].filter(c=>g.known[opp].has(c.id));}
  const fullKnown=late&&two;
  const oppCanBeat=c=>oppHand?(fullKnown?oppHand.some(o=>g.beats(o,c)):true):true;
  const oppHolds=r=>oppHand?oppHand.some(o=>o.r===r):false;
  const noisy=rng()<P.noise;

  // ----- defender -----
  if(p===g.def&&L.some(m=>m.t==='take')){
    const und=g.table.map((x,i)=>({x,i})).filter(o=>!o.x.d);
    const pool=g.hands[p].slice();const plan=[];let cost=0,ok=true;
    for(const o of und.slice().sort((a,b)=>val(b.x.a)-val(a.x.a))){
      const cands=pool.filter(c=>g.beats(c,o.x.a)).sort((a,b)=>val(a)-val(b));
      if(!cands.length){ok=false;break;}
      const c=cands[0];pool.splice(pool.indexOf(c),1);plan.push({c,i:o.i});cost+=J(c)?20:T(c)?6+rn(c):rn(c)*.4;}
    // transferring sheds a card and hands the whole attack on (back to the attacker when two play): usually strong
    const sh=L.find(m=>m.t==='show');
    if(sh&&rng()<Math.max(.5,P.transferBias))return sh; // passing the attack on for free
    const trs=L.filter(m=>m.t==='transfer'&&!J(m.c)).sort((a,b)=>val(a.c)-val(b.c));
    const tr=trs[0];
    if(tr&&rng()<P.transferBias){
      const trCost=T(tr.c)?5+rn(tr.c):rn(tr.c)*.15;
      if(!T(tr.c)||!ok||late||trCost<cost)return tr;}
    if(!ok)return {t:'take'};
    if(noisy&&rng()<.3)return {t:'take'};
    const tableVal=g.table.reduce((a,x)=>a+1+(x.d?1:0),0);
    // taking also costs the next attack, so a cheap defence is almost always better
    let takePenalty=3+tableVal*2.2+(late?14:g.deck.length<8?6:0)+Math.max(0,g.hands[p].length+tableVal-8)*1.5;
    if(P.memory&&late)takePenalty+=10;
    if(cost*P.greed>takePenalty)return {t:'take'};
    return {t:'defend',c:plan[0].c,i:plan[0].i};
  }
  const atk=L.filter(m=>m.t==='attack');
  // ----- lead -----
  if(!g.table.length){
    if(noisy)return atk[Math.floor(rng()*atk.length)];
    const h=g.hands[p];let best=null,bs=1e9;
    for(const m of atk){const c=m.c;let s=val(c);
      if((T(c)||J(c))&&!late)s+=P.leadTrumpPenalty;
      s-=1.6*(h.filter(x=>x.r===c.r).length-1);
      if(P.memory&&fullKnown&&!oppCanBeat(c))s-=12;
      // the defender is known to hold this rank: in the transfer game they would just pass it on
      if(g.mode==='perevodnoy'&&P.memory&&oppHolds(c.r))s+=4;
      if(s<bs){bs=s;best=m;}}
    return best;
  }
  // ----- throw in (main attacker or side players) -----
  const side=p!==g.att,taking=g.taking;
  const okT=atk.filter(m=>{const c=m.c;if(J(c))return late&&taking;
    if(late)return P.tossTrumpLate||!T(c)||taking;
    if(T(c))return false;
    const lim=(taking?P.tossMax+1:P.tossMax)-(side?1:0);
    return rn(c)<=lim||(P.memory&&fullKnown&&!oppCanBeat(c));});
  if(okT.length&&!noisy){okT.sort((a,b)=>val(a.c)-val(b.c));return okT[0];}
  if(noisy&&atk.length&&rng()<.5)return atk[Math.floor(rng()*atk.length)];
  return L.find(m=>m.t==='done')||L[0];
}

/* ---------------- thinking ahead (Monte Carlo) ---------------- */
// Deal the cards player p cannot see (other hands except the cards known to be there, and the deck
// except the face-up trump) at random, keeping every hand size.
function determinize(g,p,rng){
  const c=g.clone();const seen=new Set(g.hands[p].map(x=>x.id));
  const pool=[];
  for(let q=0;q<g.n;q++){if(q===p)continue;for(const x of g.hands[q])if(!g.known[q].has(x.id))pool.push(x);}
  for(const x of g.deck)if(x!==g.trumpCard)pool.push(x);
  for(let i=pool.length-1;i>0;i--){const j=Math.floor(rng()*(i+1));[pool[i],pool[j]]=[pool[j],pool[i]];}
  let k=0;
  for(let q=0;q<g.n;q++){if(q===p)continue;c.hands[q]=g.hands[q].map(x=>g.known[q].has(x.id)?x:pool[k++]);}
  const nd=g.deck.length;c.deck=[];if(nd){c.deck.push(g.trumpCard);for(let i=1;i<nd;i++)c.deck.push(pool[k++]);}
  return c;}
// how good the position is for p: fewer and stronger cards than the others; the game result if it ended
function evaluate(g,p){
  if(g.over&&g.teams)return g.loserTeam==null?0:g.loserTeam===g.teams[p]?-100:100;
  if(g.over)return g.fool===p?-100:g.fool===-1?0:(g.out.indexOf(p)>=0?100-g.out.indexOf(p)*5:60);
  if(!g.active(p))return 100-g.out.indexOf(p)*5;
  const top=g.ranks.length-1,late=g.deck.length===0;
  // a card in hand is a burden, but high trumps and jokers are worth keeping for later
  const keep=c=>c.r==='J'?7:g.isTrump(c)?2.5+3*g.rk(c)/top:2*Math.pow(g.rk(c)/top,2);
  const weak=q=>{const h=g.hands[q];let s=h.length*(late?4:2.4);for(const c of h)s-=keep(c)*(late?.6:.8);return s;};
  if(g.teams){let mine=0,their=0,nm=0,nt=0;for(let q=0;q<g.n;q++){if(!g.active(q))continue;if(g.teams[q]===g.teams[p]){mine+=weak(q);nm++;}else{their+=weak(q);nt++;}}
    return nt?(their/nt-mine/Math.max(1,nm))*3:50;}
  const mine=weak(p);let worst=-1e9,sum=0,n=0;
  for(let q=0;q<g.n;q++){if(q===p||!g.active(q))continue;const w=weak(q);sum+=w;n++;if(w>worst)worst=w;}
  // in a crowd it is enough not to be the weakest; head to head every card counts
  return n?((worst+sum/n)/2-mine)*3:50;}
function rollout(g,p,horizon,rng){
  const stopAt=g.bouts+horizon;let guard=0;
  while(!g.over&&g.bouts<stopAt&&guard++<400){const q=g.toMove();const m=heuristicMove(g,q,ROLL,rng);if(!m||!g.apply(q,m))break;}
  return evaluate(g,p);}
function mcMove(g,p,P,rng,L){
  // identical attack cards of one rank and suit-less duplicates are rare; keep every legal move as a candidate
  const cands=L.slice(0,14),stats=cands.map(()=>({s:0,n:0}));
  const t0=now(),ms=P.mc.ms,H=P.mc.horizon;let it=0;
  while(now()-t0<ms||it<cands.length*4){
    const d=determinize(g,p,rng);
    for(let i=0;i<cands.length;i++){const c=d.clone();const m=mapMove(c,cands[i]);if(!c.apply(p,m))continue;stats[i].s+=rollout(c,p,H,rng);stats[i].n++;}
    if(++it>400)break;}
  let best=-1,bv=-1e9;stats.forEach((s,i)=>{if(s.n){const v=s.s/s.n;if(v>bv){bv=v;best=i;}}});
  const h=heuristicMove(g,p,P,rng,L),hi=cands.findIndex(m=>m.t===h.t&&m.c===h.c&&m.i===h.i);
  if(hi>=0&&stats[hi].n&&bv-stats[hi].s/stats[hi].n<(P.mc.margin||4))return h;
  return best>=0?cands[best]:null;}
// moves refer to card objects, which are shared between copies, so they carry over as they are
function mapMove(c,m){return m;}


;
// Progression data: campaign, goals, shop, achievements, daily gift, statistics.
// Goals: 'win', 'first', and numbered ones: takeN (won taking at most N times), fastN (won within N bouts),
// transferN (won after at least N transfers). Old names stay readable for old saves.
const GOAL_ALIAS={noTake:'take0',fast:'fast16',transfer:'transfer2'};
const times=n=>n===1?'одного раза':n+' раз';
const wordN=(n,a,b,c)=>{const m=n%10,h=n%100;return n+' '+(m===1&&h!==11?a:m>=2&&m<=4&&(h<12||h>14)?b:c);};
function goalParse(k){k=GOAL_ALIAS[k]||k;const m=/^(take|fast|transfer)(\d+)$/.exec(k);return m?{k:m[1],n:+m[2]}:{k};}
function goalInfo(key){const {k,n}=goalParse(key);
  if(k==='win')return {t:'Не остаться дураком',short:'Победа',d:'победите'};
  if(k==='first')return {t:'Выйти из игры первым',short:'Первым',d:'выйдите из игры первым'};
  if(k==='pogony')return {t:'Повесить погоны',short:'Погоны',d:'повесьте сопернику погоны'};
  if(k==='take')return n===0?{t:'Победить, ни разу не взяв',short:'Без взяток',d:'победите, ни разу не взяв'}:
    {t:`Победить, взяв не больше ${times(n)}`,short:`≤ ${n} ${n===1?'взятки':'взяток'}`,d:`победите, взяв не больше ${times(n)}`};
  if(k==='fast')return {t:`Победить за ${wordN(n,'ход','хода','ходов')} или быстрее`,short:`≤ ${wordN(n,'хода','ходов','ходов')}`,d:`победите за ${wordN(n,'ход','хода','ходов')} или быстрее`};
  if(k==='transfer')return n===1?{t:'Победить, хотя бы раз переведя',short:'Перевод',d:'победите, хотя бы раз переведя'}:
    {t:`Победить, переведя хотя бы ${n} раза`,short:`${n} перевода`,d:`победите, переведя хотя бы ${n} раза`};
  return {t:key,short:key,d:key};}
const GOALS=new Proxy({},{get:(o,k)=>goalInfo(String(k))});
// r = everything known about the finished game from the player's side
function goalMet(key,r){const {k,n}=goalParse(key),win=r.win;switch(k){
  case'win':return win;case'first':return r.firstOut;case'pogony':return win&&r.pogGiven;
  case'take':return win&&r.takes<=n;case'fast':return win&&r.bouts<=n;case'transfer':return win&&r.transfers>=n;}return false;}
// The road to the tsar: ten places, each with its own house rules. Goals are fitted by simulation (autoGoals).
const RULE_TEXT={open:'карты соперника открыты',dark:'козырь спрятан под платком',fog:'не видно, сколько карт у соперников',
  neighbors:'подкидывают только соседи',show:'перевод показом козыря',chest:'в колоде спрятан клад',timer:'на каждый ход 12 секунд',noLimit:'подкидывать можно без лимита',cheat:'Кощей жульничает — лови!',teams:'пара на пару: напротив — ваш напарник'};
const LOCS=[
  {id:'village',name:'Деревня',table:'sukno',rule:'Классический подкидной',story:'Глашатай прокричал: царь объявил турнир по дураку, победителю — полцарства! Начинать придётся с родной деревни.',
   stages:[{name:'Учёба у пастуха',opps:['vanka'],mode:'podkidnoy',deck:36,rules:{open:true},goals:['win','take2','fast18']},
           {opps:['kuzmich'],mode:'podkidnoy',deck:36},
           {opps:['nura'],mode:'podkidnoy',deck:36},
           {name:'Деревенский турнир',opps:['kuzmich','nura','vanka'],mode:'podkidnoy',deck:36,boss:1}]},
  {id:'fair',name:'Ярмарка',table:'yarmarka',rule:'Переводной дурак',story:'На ярмарке играют на переводного: отбиваться не хочешь — переведи следующему.',
   stages:[{opps:['tishka'],mode:'perevodnoy',deck:36},
           {opps:['matryona'],mode:'podkidnoy',deck:36},
           {opps:['kupets'],mode:'perevodnoy',deck:36},
           {name:'Ярмарочный стол',opps:['tishka','matryona','kupets'],mode:'perevodnoy',deck:36,boss:1}]},
  {id:'inn',name:'Постоялый двор',table:'izba',rule:'Короткая колода на 24 карты',story:'На тракте играют быстро: колода с девяток, пока ямщик лошадей меняет.',
   stages:[{opps:['erofey'],mode:'podkidnoy',deck:24},
           {opps:['pelageya'],mode:'perevodnoy',deck:24},
           {opps:['foma'],mode:'podkidnoy',deck:24,rules:{noLimit:true}},
           {name:'Ночь на постоялом',opps:['erofey','pelageya','foma'],mode:'perevodnoy',deck:24,rules:{noLimit:true},boss:1}]},
  {id:'town',name:'Город',table:'barhat',rule:'Большая колода с джокерами',story:'В городе играют большой колодой — с двойками и джокерами. Джокер бьёт любую карту.',
   stages:[{opps:['prokhor'],mode:'podkidnoy',deck:54},
           {opps:['aglaya'],mode:'perevodnoy',deck:54},
           {opps:['akim'],mode:'podkidnoy',deck:54},
           {name:'Городской клуб',opps:['prokhor','aglaya','akim'],mode:'podkidnoy',deck:54,boss:1}]},
  {id:'hut',name:'Избушка Бабы-Яги',table:'izba',rule:'Тёмный козырь',story:'Избушка повернулась к тебе передом. Яга прячет козырь под платком — масть узнаешь, когда кто-нибудь им побьёт.',
   stages:[{opps:['bayun'],mode:'perevodnoy',deck:36,rules:{dark:true}},
           {opps:['leshy','bayun'],mode:'podkidnoy',deck:36,rules:{dark:true}},
           {opps:['yaga'],mode:'perevodnoy',deck:36,rules:{dark:true}},
           {name:'Ступа и помело',opps:['yaga','leshy','bayun'],mode:'perevodnoy',deck:36,rules:{dark:true,fog:true},boss:1}]},
  {id:'outpost',name:'Богатырская застава',table:'sukno',rule:'Подкидывают только соседи',story:'У богатырей порядок: подкидывает только тот, кто ходит, да сосед отбивающегося.',
   stages:[{opps:['alesha','dobrynya'],mode:'podkidnoy',deck:36,rules:{neighbors:true}},
           {opps:['ilya','alesha'],mode:'perevodnoy',deck:36,rules:{neighbors:true}},
           {opps:['dobrynya','alesha','prokhor'],mode:'podkidnoy',deck:52,rules:{neighbors:true}},
           {name:'Богатырский пир',opps:['ilya','dobrynya','alesha','voevoda'],mode:'perevodnoy',deck:52,rules:{neighbors:true},boss:1}]},
  {id:'merchant',name:'Купеческий дом',table:'yarmarka',rule:'Перевод показом козыря и клад',story:'У купцов можно перевести, лишь показав козырь. А в колоде спрятан клад — кому достанется?',
   stages:[{opps:['mitrofan'],mode:'perevodnoy',deck:36,rules:{show:true,chest:true}},
           {opps:['varvara'],mode:'perevodnoy',deck:52,rules:{show:true,chest:true}},
           {opps:['mitrofan','varvara'],mode:'perevodnoy',deck:52,rules:{show:true,chest:true}},
           {name:'Купеческая сделка',opps:['varvara','kupets','mitrofan'],mode:'perevodnoy',deck:52,rules:{show:true,chest:true},boss:1}]},
  {id:'terem',name:'Боярский терем',table:'palaty',rule:'Ход на время',story:'Бояре не любят ждать: на каждый ход — двенадцать ударов сердца.',
   stages:[{opps:['voevoda'],mode:'podkidnoy',deck:36,rules:{timer:true}},
           {opps:['klyuchnitsa'],mode:'perevodnoy',deck:52,rules:{timer:true}},
           {opps:['boyarin'],mode:'perevodnoy',deck:36,rules:{timer:true}},
           {name:'Боярская дума',opps:['voevoda','klyuchnitsa','boyarin','akim'],mode:'perevodnoy',deck:52,rules:{timer:true},boss:1}]},
  {id:'koschei',name:'Кощеево царство',table:'barhat',rule:'Туман и шулер',story:'В Кощеевом царстве всё в тумане, а сам Кощей жульничает. Заметил неправильную карту на столе — жми «Поймал!».',
   stages:[{opps:['kikimora'],mode:'perevodnoy',deck:36,rules:{fog:true}},
           {opps:['gorynych'],mode:'podkidnoy',deck:52,rules:{fog:true}},
           {opps:['kikimora','gorynych'],mode:'perevodnoy',deck:36,rules:{fog:true}},
           {name:'Кощей Бессмертный',opps:['koschei'],mode:'perevodnoy',deck:36,rules:{cheat:true},boss:1}]},
  {id:'palace',name:'Царский двор',table:'palaty',rule:'Финал — парный дурак',story:'Двери палат открыты. Развесели царевну, обыграй царя — а на пиру Несмеяна сядет с тобой в пару против царя и Кощея.',
   stages:[{opps:['nesmeyana'],mode:'perevodnoy',deck:36,rules:{show:true}},
           {opps:['nesmeyana','boyarin'],mode:'podkidnoy',deck:36},
           {name:'Царь Горох',opps:['tsar'],mode:'perevodnoy',deck:36,rules:{show:true},boss:1},
           {name:'Царский пир: пара на пару',opps:['tsar','nesmeyana','koschei'],mode:'podkidnoy',deck:36,rules:{teams:true},boss:1}]}
];
// Extra goals for a stage, numbers measured on a strong player (≈ a third to a half of the wins meet each).
function autoGoals(st,li,si){const n=st.opps.length+1,d=st.deck,big=d>=52,per=st.mode==='perevodnoy',r=st.rules||{};
  const take=n===2?(d===24?0:d===36?1:5):n===3?(d===24||d===36?0:d===54?2:1):(big?1:0);
  const fast=d===24?8:d===36?14:33;
  const pool=[];
  if(n===2){pool.push('take'+take,'fast'+fast);if(per)pool.push('transfer'+(r.show?3:2));}
  else{pool.push('first','take'+take);if(per)pool.push('transfer'+(n===3?2:1));}
  const k=(li*7+si*3)%pool.length;const a=pool[k],b=pool[(k+1)%pool.length];
  return ['win',a,b];}
LOCS.forEach((L,li)=>L.stages.forEach((st,si)=>{if(!st.goals)st.goals=autoGoals(st,li,si);}));
const STARS_MAX=LOCS.reduce((a,l)=>a+l.stages.length*3,0);
const SHOP={
  backs:[{id:'gzhel',name:'Гжель',price:0},{id:'hohloma',name:'Хохлома',price:900},{id:'matr',name:'Матрёшки',price:1200},{id:'gorodets',name:'Городец',price:1500},
         {id:'mezen',name:'Мезень',price:1800},{id:'zhostovo',name:'Жостово',price:2400},{id:'kruzhevo',name:'Вологодское кружево',price:2600},{id:'pavlov',name:'Павловский платок',price:3000},{id:'boyar',name:'Боярская',price:-1,how:'Только в «Боярском пакете» (Казна)'},{id:'palekh',name:'Палех',price:3500},{id:'tsar',name:'Царская',price:-1,how:'Награда за Царский пир'}],
  faces:[{id:'classic',name:'Классическая',price:0},{id:'big',name:'Крупные знаки',price:300,d:'Большие значки — удобно на телефоне'},{id:'four',name:'Четыре цвета',price:700,d:'Каждая масть своим цветом'},{id:'night',name:'Ночная',price:1000,d:'Тёмные карты — не слепят вечером'},
         {id:'lubok',name:'Лубок',price:1500,d:'Яркая народная картинка'},
         {id:'russ',name:'Русская',price:2200,d:'Цари, царицы и богатыри'},{id:'skaz',name:'Сказочная',price:-1,d:'Царь, Яга, Кощей и другие герои игры',how:'Награда за первую победу в игре с друзьями (скоро)'},{id:'gold',name:'Золотая',price:-1,how:'Награда за все 120 звёзд'}],
  tables:[{id:'sukno',name:'Зелёное сукно',price:0},{id:'barhat',name:'Синий бархат',price:1200},{id:'dacha',name:'Дачная веранда',price:1800},{id:'izba',name:'Изба',price:2000},{id:'kupe',name:'Купе поезда',price:2500},
          {id:'yarmarka',name:'Ярмарка',price:3000},{id:'morozko',name:'Морозко',price:-1,how:'Награда за 7 выполненных заданий дня'},{id:'palaty',name:'Царские палаты',price:-1,how:'Награда за победу над царём'}]
};
const GIFTS=[20,30,40,50,60,80,150];
const ACH=[
  {id:'w1',name:'Первая победа',d:'Выиграть партию',f:s=>s.wins>=1,c:20},
  {id:'w10',name:'Знаток',d:'Выиграть 10 партий',f:s=>s.wins>=10,c:50},
  {id:'w50',name:'Мастер стола',d:'Выиграть 50 партий',f:s=>s.wins>=50,c:150},
  {id:'g100',name:'Завсегдатай',d:'Сыграть 100 партий',f:s=>s.games>=100,c:150},
  {id:'pogG',name:'Погоны вручены',d:'Повесить сопернику погоны',f:s=>s.pogGiven>=1,c:50},
  {id:'pogR',name:'Ну и погоны…',d:'Получить погоны самому',f:s=>s.pogGot>=1,c:20},
  {id:'clean',name:'Неприкасаемый',d:'Победить, ни разу не взяв',f:s=>s.noTakeWins>=1,c:50},
  {id:'st5',name:'Полоса удачи',d:'5 побед подряд',f:s=>s.bestStreak>=5,c:100},
  {id:'tr20',name:'Переводчик',d:'Сделать 20 переводов',f:s=>s.transfers>=20,c:50},
  {id:'m4',name:'Шумная компания',d:'Победить за столом на 4 игрока или больше',f:s=>s.bigWins>=1,c:50},
  {id:'m6',name:'Полный стол',d:'Не остаться дураком за столом на 6',f:s=>s.sixWins>=1,c:100},
  {id:'j54',name:'С джокерами',d:'Победить с колодой на 54 карты',f:s=>s.win54>=1,c:40},
  {id:'loc1',name:'Деревенский чемпион',d:'Пройти Деревню',f:s=>s.locsDone>=1,c:60},
  {id:'loc2',name:'Гроза ярмарки',d:'Пройти Ярмарку',f:s=>s.locsDone>=2,c:80},
  {id:'loc3',name:'Бывалый путник',d:'Пройти Постоялый двор',f:s=>s.locsDone>=3,c:100},
  {id:'loc4',name:'Городской знаток',d:'Пройти Город',f:s=>s.locsDone>=4,c:120},
  {id:'loc5',name:'Перехитрил Ягу',d:'Пройти Избушку Бабы-Яги',f:s=>s.locsDone>=5,c:150},
  {id:'loc6',name:'Названый богатырь',d:'Пройти Богатырскую заставу',f:s=>s.locsDone>=6,c:170},
  {id:'loc7',name:'Купеческий гость',d:'Пройти Купеческий дом',f:s=>s.locsDone>=7,c:190},
  {id:'loc8',name:'Боярский гость',d:'Пройти Боярский терем',f:s=>s.locsDone>=8,c:220},
  {id:'loc9',name:'Нашёл иглу',d:'Пройти Кощеево царство',f:s=>s.locsDone>=9,c:260},
  {id:'loc10',name:'Полцарства',d:'Пройти Царский двор',f:s=>s.locsDone>=10,c:400},
  {id:'s30',name:'Звёздный путь',d:'Собрать 40 звёзд в походе',f:s=>s.stars>=40,c:120},
  {id:'s60',name:'Звездочёт',d:'Собрать 80 звёзд в походе',f:s=>s.stars>=80,c:200},
  {id:'s120',name:'Все звёзды',d:'Собрать все 120 звёзд',f:s=>s.stars>=120,c:400},
  {id:'col',name:'Коллекционер',d:'Собрать 6 предметов в лавке',f:s=>s.owned>=6,c:100}
];


/* ---------- rules of the economy, the same in the browser and on the server ---------- */
const DAILY_REWARD=80;
// the day runs on Moscow time for everyone, so a gift or a task is the same wherever the player is
function dayOf(t){const d=new Date(t+3*3600e3);return d.getUTCFullYear()+'-'+(d.getUTCMonth()+1)+'-'+d.getUTCDate();}
function prevDayOf(t){return dayOf(t-86400e3);}
function dailyTaskFor(d,alt){let h=7;for(const ch of d)h=(h*31+ch.charCodeAt(0))>>>0;
  // a task swapped for another stays swapped for the rest of the day
  if(alt&&alt.day===d)h=(h^(alt.n*2654435761))>>>0;const r=makeRng(h);
  const mode=r()<.5?'podkidnoy':'perevodnoy',deck=r()<.3?54:36,players=2+Math.floor(r()*3),big=deck===54;
  // goal numbers fitted by simulation so a good player manages them in roughly a third of the wins or more
  const pool=['take'+(players===2?(big?5:1):players===3?(big?1:0):(big?1:0))];
  if(mode==='perevodnoy')pool.push('transfer'+(players===4?1:2));
  if(players>2)pool.push('first');else pool.push('fast'+(big?34:14));
  const goal=pool[Math.floor(r()*pool.length)];return {mode,deck,players,goal};}
function freshEco(){return {coins:0,owned:['gzhel','sukno','classic'],back:'gzhel',face:'classic',tableSkin:'sukno',
  camp:{},daily:{day:'',done:false},gift:{day:'',streak:0},ach:{},iap:{},iapDone:{},xp:0,lvl:1,
  st:{games:0,wins:0,losses:0,draws:0,streak:0,bestStreak:0,pogGiven:0,pogGot:0,noTakeWins:0,transfers:0,takes:0,firstOuts:0,bigWins:0,sixWins:0,win54:0,dailyCount:0,coinsEarned:0,
      byMode:{podkidnoy:{g:0,w:0},perevodnoy:{g:0,w:0}},byDeck:{36:{g:0,w:0},54:{g:0,w:0}},byPlayers:{}}};}
const ECO_KEYS=['xp','lvl','coins','owned','back','face','tableSkin','camp','daily','dailyAlt','gift','ach','iap','iapDone','st','adCoins','netDay','bail','inbox','nid','seen'];
// levels grow with every game played and never go down; a new level brings coins
function xpFor(L){return 25*(L-1)*L;} // experience needed to reach level L: 50, 150, 300, 500…
const LEVEL_COINS=L=>50*L;
function campStars(camp){let n=0;for(const k in camp)n+=camp[k].stars.reduce((a,b)=>a+b,0);return n;}
function campRec(camp,l,i){return camp[l+'.'+i]||{won:false,stars:[0,0,0]};}
function campLocDone(camp,li){return campRec(camp,LOCS[li].id,LOCS[li].stages.length-1).won;}
function campLocsDone(camp){let n=0;LOCS.forEach((l,i)=>{if(campLocDone(camp,i))n++;});return n;}
function achDue(eco){const s=Object.assign({},eco.st,{stars:campStars(eco.camp),locsDone:campLocsDone(eco.camp),owned:eco.owned.length});return ACH.filter(a=>!eco.ach[a.id]&&a.f(s));}
function shopItem(id){for(const k of ['backs','faces','tables']){const it=SHOP[k].find(x=>x.id===id);if(it)return Object.assign({kind:k},it);}return null;}

/* ---------- rewards for games with bots ---------- */
const CHEST_COINS=30,CAUGHT_COINS=10;
function stageReward(li,si,rec){const st=LOCS[li].stages[si];return rec.won?8+3*li:40+25*li+(st.boss?100+20*li:0);}
const POOLS={1:['vanka','kuzmich'],2:['nura','tishka','matryona','prokhor','aglaya','erofey','pelageya','mitrofan'],3:['kupets','akim','voevoda','klyuchnitsa','foma','bayun','leshy','alesha','dobrynya','varvara','kikimora'],4:['boyarin','nesmeyana','yaga','ilya','gorynych']};
const LEVELS={easy:{name:'Лёгкие',mult:1,from:[1,2]},medium:{name:'Средние',mult:1.5,from:[2,1]},hard:{name:'Сильные',mult:2.2,from:[3,4,2]},mixed:{name:'Вперемешку',mult:1.6,from:'mix'}};
const quickReward=(k,level)=>Math.round(8*k*LEVELS[level].mult+6);
// who may sit at a quick table of this level (the strongest come only after they were beaten on the road)
function levelPool(level,camp){const L=LEVELS[level]||LEVELS.medium;let pool=[];
  if(L.from==='mix')pool=[...POOLS[1],...POOLS[2],...POOLS[3]];else for(const lv of L.from)pool.push(...POOLS[lv]);
  if(level==='hard'&&campRec(camp,'koschei',3).won)pool.unshift('koschei');
  if(level==='hard'&&campRec(camp,'palace',2).won)pool.unshift('tsar');
  return pool;}


;
// Generated from chars.js by build.py: how each character plays (the server needs it too).
const CHAR_AI={vanka:{style:'easy',over:{noise:.35}},kuzmich:{style:'easy',over:{}},nura:{style:'sly',over:{}},tishka:{style:'sly',over:{transferBias:1,multi:.9}},matryona:{style:'bold',over:{}},kupets:{style:'shrewd',over:{}},prokhor:{style:'bold',over:{noise:.06}},akim:{style:'shrewd',over:{multi:.3}},aglaya:{style:'sly',over:{greed:1.2}},voevoda:{style:'bold',over:{noise:.03,greed:.8}},klyuchnitsa:{style:'shrewd',over:{multi:.7}},boyarin:{style:'master',over:{transferBias:.5}},nesmeyana:{style:'master',over:{multi:.4,transferBias:.9}},erofey:{style:'bold',over:{noise:.1}},pelageya:{style:'sly',over:{}},foma:{style:'shrewd',over:{mc:{ms:30,horizon:2}}},bayun:{style:'sly',over:{transferBias:1}},leshy:{style:'bold',over:{noise:.05,greed:.75}},yaga:{style:'master',over:{mc:{ms:80,horizon:3}}},alesha:{style:'sly',over:{multi:.9}},dobrynya:{style:'shrewd',over:{}},ilya:{style:'master',over:{greed:.85}},mitrofan:{style:'sly',over:{}},varvara:{style:'shrewd',over:{multi:.6}},kikimora:{style:'sly',over:{transferBias:1,multi:.8}},gorynych:{style:'bold',over:{greed:.65,tossMax:6}},koschei:{style:'master',over:{mc:{ms:130,horizon:3},searchBudget:40000,cheat:true}},tsar:{style:'master',over:{searchBudget:40000}}};
function charAI(id){const c=CHAR_AI[id]||{style:'bold',over:{}};return Object.assign({},STYLES[c.style],c.over);}

;
// Friends' table: the authoritative game on the server.
// A room is a plain JSON object kept in the database. The game itself is not stored: it is rebuilt
// from the seed and the log of moves on every request (a few hundred moves at most), so the stored
// record stays small and every client can be brought up to date from any point.
// Needs Game, makeRng (engine.js) and aiMove, STYLES (ai.js) in scope.

const ROOM_TTL=6*3600*1000;
const BOT_CHARS=['kuzmich','nura','tishka','matryona','kupets','prokhor','akim','aglaya','erofey','pelageya','foma','varvara','mitrofan','klyuchnitsa'];
const BOT_STYLE={easy:'easy',medium:'bold',hard:'shrewd'};
const CODE_WORDS=['КОТ','ЁЖ','СОМ','ЁРШ','ЖУК','ЛЕВ','ЯК','ГУСЬ','ЛОСЬ','ВОЛК','ЛИС','БОБР','КИТ','СЫЧ','ТУР','ЗУБР','ОСА','ЯЗЬ','ВОЛ','ГРАЧ'];
const PHRASES=['Привет!','Ходи!','Ну ты даёшь!','Эх…','Хорошая игра!','Быстрее!','Ха-ха!','Спасибо!','Сейчас отыграюсь','Ой, всё','👍','😂','😮','😡','🎉','🙈'];
const MAX_PLAYERS={24:4,36:5,52:6,54:6};

function rndToken(rnd){let s='';for(let i=0;i<20;i++)s+='abcdefghijkmnpqrstuvwxyz23456789'[Math.floor(rnd()*32)];return s;}
function makeCode(rnd){return CODE_WORDS[Math.floor(rnd()*CODE_WORDS.length)]+'-'+(100+Math.floor(rnd()*900));}
// codes are typed by people: accept latin look-alikes, spaces, any case
function normCode(s){s=String(s||'').toUpperCase().replace(/\s+/g,'').replace(/Ё/g,'Ё');
  const lat={A:'А',B:'В',C:'С',E:'Е',H:'Н',K:'К',M:'М',O:'О',P:'Р',T:'Т',X:'Х',Y:'У'};s=s.replace(/[ABCEHKMOPTXY]/g,ch=>lat[ch]);
  const m=/^([А-ЯЁ]+)-?(\d{3}|\d{8})$/.exec(s);return m?m[1]+'-'+m[2]:'';}
function cleanName(s){s=String(s||'').replace(/[<>&"'`\\]/g,'').replace(/\s+/g,' ').trim().slice(0,14);return s||'Игрок';}

function sanitizeOpts(o){o=o||{};const deck=[24,36,52,54].includes(+o.deck)?+o.deck:36;
  const n=Math.max(2,Math.min(+o.n||2,MAX_PLAYERS[deck]));const mode=o.mode==='perevodnoy'?'perevodnoy':'podkidnoy';
  const R=o.rules||{},rules={};
  for(const k of ['neighbors','noLimit','open','fog','dark','chest','cheat','teams','show','nohint'])if(R[k])rules[k]=true;
  if(rules.teams&&n!==4)delete rules.teams;
  if(rules.show&&mode!=='perevodnoy')delete rules.show;
  if(rules.open&&rules.fog)delete rules.fog;
  const timer=[15,30,60].includes(+o.timer)?+o.timer:30;
  const level=['easy','medium','hard'].includes(o.level)?o.level:'medium';
  return {deck,n,mode,rules,timer,level};}

function newRoom(opts,name,now,rnd,ac,q){
  const o=sanitizeOpts(opts),tok=rndToken(rnd);
  const room={code:makeCode(rnd),v:1,born:now,exp:now+ROOM_TTL,opts:o,host:0,st:'lobby',seed:0,game:0,log:[],at:now,dl:0,chat:[],ci:0,fin:null,seats:[]};
  // an open table (quick game): it starts by itself after a short wait, and the game has a stake
  if(q){room.q=q;room.qAt=now+QUICK_WAIT;}
  for(let i=0;i<o.n;i++)room.seats.push(i===0?Object.assign({k:'h',nm:cleanName(name),tok,seen:now},ac?{ac}:{}):{k:'o'});
  return {room,seat:0,tok};}

// a game of one player with bots (the road, a quick game, the task of the day): the same table, run here
function soloOpts(o){const deck=[24,36,52,54].includes(+o.deck)?+o.deck:36;const n=Math.max(2,Math.min(+o.n||2,MAX_PLAYERS[deck]));
  const mode=o.mode==='perevodnoy'?'perevodnoy':'podkidnoy',R=o.rules||{},rules={};
  for(const k of ['neighbors','noLimit','open','fog','dark','chest','cheat','teams','show','timer'])if(R[k])rules[k]=true;
  if(rules.teams&&n!==4)delete rules.teams;if(rules.show&&mode!=='perevodnoy')delete rules.show;if(rules.open&&rules.fog)delete rules.fog;if(rules.neighbors&&n<3)delete rules.neighbors;
  return {deck,n,mode,rules,timer:rules.timer?12:0,level:['easy','medium','hard','mixed'].includes(o.level)?o.level:'medium'};}
function newSolo(o,chars,solo,name,now,rnd,ac){
  const tok=rndToken(rnd),opts=soloOpts(Object.assign({},o,{n:chars.length+1}));
  // a long code nobody will guess or type: only the player knows it
  const room={code:makeCode(rnd)+String(Math.floor(rnd()*1e5)).padStart(5,'0'),v:1,born:now,exp:now+ROOM_TTL,opts,host:0,st:'lobby',seed:0,game:0,log:[],at:now,dl:0,chat:[],ci:0,fin:null,solo,
    seats:[Object.assign({k:'h',nm:cleanName(name),tok,seen:now},ac?{ac}:{}),...chars.map(ch=>({k:'b',ch}))]};
  start(room,null,now,rnd);return {room,tok};}

function seatOf(room,tok){return tok?room.seats.findIndex(s=>s.k==='h'&&s.tok===tok):-1;}
function humans(room){return room.seats.filter(s=>s.k==='h').length;}

function join(room,name,now,rnd,tok,ac){
  const was=seatOf(room,tok);if(was>=0){room.seats[was].seen=now;room.seats[was].away=false;return {seat:was,tok};}
  if(room.st!=='lobby'){ // a game is on: a newcomer may take over a seat a bot is keeping for someone who left
    return {err:'started'};}
  const i=room.seats.findIndex(s=>s.k==='o');if(i<0)return {err:'full'};
  const t=rndToken(rnd);room.seats[i]=Object.assign({k:'h',nm:cleanName(name),tok:t,seen:now},ac?{ac}:{});room.v++;
  // a full open table does not wait any longer
  if(room.q&&!room.seats.some(s=>s.k==='o'))room.qAt=room.qAt?Math.min(room.qAt,now+1500):now+1500;
  return {seat:i,tok:t};}

// host changes the table before the start: options, or a seat between "open" and "bot"
function configure(room,tok,ch){
  if(room.q)return 'quick';
  if(seatOf(room,tok)!==room.host||room.st==='play')return 'not host';
  if(ch.opts){const o=sanitizeOpts(Object.assign({},room.opts,ch.opts));
    const hs=room.seats.filter(s=>s.k==='h');if(o.n<hs.length)o.n=hs.length;
    const seats=[];for(const s of room.seats)if(s.k==='h')seats.push(s);
    // keep humans first in their order, then previous bots/open seats
    const rest=room.seats.filter(s=>s.k!=='h');while(seats.length<o.n)seats.push(rest.shift()||{k:'o'});
    // the host must stay the host
    const hostTok=room.seats[room.host].tok;room.seats=seats;room.host=seats.findIndex(s=>s.tok===hostTok);
    room.opts=sanitizeOpts(o);if(room.opts.n!==seats.length){room.opts.n=seats.length;}}
  if(ch.seat!=null){const s=room.seats[ch.seat];if(!s)return 'bad seat';
    if(s.k==='o')room.seats[ch.seat]={k:'b'};else if(s.k==='b')room.seats[ch.seat]={k:'o'};
    else if(s.k==='h'&&ch.seat!==room.host&&ch.kick)room.seats[ch.seat]={k:'o'};}
  room.v++;return null;}

function start(room,tok,now,rnd){
  // open tables and games with bots start by themselves; a table a player set up in the list is started by its host (bots take the empty seats)
  if((room.q||room.solo)&&tok!==null&&!(room.q&&room.q.list&&room.st==='lobby'&&seatOf(room,tok)===room.host))return 'quick';
  if(!room.q&&!room.solo&&seatOf(room,tok)!==room.host)return 'not host';if(room.st==='play')return 'already';
  const used=new Set();
  room.seats.forEach((s,i)=>{if(s.k==='h'){s.away=false;s.idle=false;s.to=0;return;}
    if(room.q)s.ch=null;
    let ch=s.ch&&!used.has(s.ch)?s.ch:null;
    if(!ch){const pool=BOT_CHARS.filter(c=>!used.has(c));ch=pool[Math.floor(rnd()*pool.length)];}
    used.add(ch);room.seats[i]={k:'b',ch};});
  room.st='play';room.seed=1+Math.floor(rnd()*2147483646);room.game++;room.log=[];room.fin=null;room.at=now;room.dl=0;room.cc=0;
  room.chest=-1;
  if(room.opts.rules.chest){const left=room.opts.deck-room.opts.n*6;if(left>=3)room.chest=1+Math.floor(rnd()*(left-1));} // index in the deck array, never the trump at 0
  room.v++;schedule(room,now);return null;}

/* ---------- rebuilding the game ---------- */
function gameOpts(room){const o=room.opts,R=o.rules;
  return {mode:o.mode,deck:o.deck,players:o.n,teams:R.teams&&o.n===4?[0,1,0,1]:null,
    rules:{neighbors:!!R.neighbors,show:!!R.show,noLimit:!!R.noLimit,cheat:!!R.cheat},rng:makeRng(room.seed)};}
// same as Game.prototype.settle, but remembers who was passed over automatically,
// so the clients (who cannot see those hands) can follow without guessing
function settleRec(){
  if(this.over||!this.table.length)return;
  if(!this.taking&&this.undefended().length>0)return;
  if(!this.taking&&this.hands[this.def].length===0)return this.endBout(false);
  // at a table with people nobody is passed over for having nothing to add: that would tell the others what is not in the hand.
  // Only when the table is full (public knowledge) the round ends by itself.
  const full=this.table.length>=this.limit||(!this.taking&&this.undefended().length>=this.hands[this.def].length);
  for(const q of this.throwers()){if(this.passed.has(q))continue;if(this._noAuto&&!full)return;if(this.hands[q].some(c=>this.canAttack(q,c)))return;this.passed.add(q);this._ap.push(q);}
  this.endBout(this.taking);}
function card(g,p,id){return g.hands[p].find(c=>c.id===id)||null;}
function applyMove(g,p,m){const c=m.c?card(g,p,m.c):null;
  switch(m.t){
    case'attack':return !!c&&g.attack(p,c);
    case'defend':return !!c&&g.defend(p,c,m.i);
    case'transfer':return !!c&&g.transfer(p,c);
    case'show':return !!c&&g.show(p,c);
    case'take':return g.take(p);
    case'done':return g.done(p);
    case'cd':return !!c&&g.cheatDefend(p,c,m.i);
    case'ca':return !!c&&g.cheatAttack(p,c);
    case'acc':return g.accuse(p);}
  return false;}
// build the game; meta[i] tells what log entry i caused: its events and the automatic passes
function build(room){
  const g=new Game(gameOpts(room));g.settle=settleRec;g._noAuto=!room.solo;g.events=[];const meta=[];
  for(const e of room.log){g._ap=[];const e0=g.events.length;applyMove(g,e.p,e);meta.push({e0,e1:g.events.length,ap:g._ap});}
  g._ap=[];return {g,meta};}

/* ---------- moves ---------- */
function lastRun(room,g){const l=room.log[room.log.length-1];
  return l&&(l.t==='attack'||l.t==='ca')&&l.p!==g.def&&g.table.length?l.p:-1;}
function mayAct(room,g,p,m){
  if(g.over||!g.active(p))return false;
  if(m.t==='acc')return !!g.rules.cheat&&g.table.length>0;
  const tm=g.toMove();
  if((m.t==='attack'||m.t==='ca')&&p!==g.def&&lastRun(room,g)===p)return true; // add more cards before the defender answers
  return tm===p;}
function act(room,tok,m,now){
  const p=seatOf(room,tok);if(p<0)return 'not seated';if(room.st!=='play')return 'no game';
  room.seats[p].seen=now;room.seats[p].away=false;room.seats[p].idle=false;room.seats[p].to=0;
  const {g}=build(room);g._ap=[];
  m={t:String(m.t),c:m.c!=null?String(m.c):undefined,i:m.i!=null?+m.i:undefined};
  if(!mayAct(room,g,p,m))return 'not your turn';
  if(!applyMove(g,p,m))return 'illegal';
  push(room,p,m,now);finishIfOver(room,g,now);schedule(room,now,g);return null;}
function push(room,p,m,now,auto){const e={p,t:m.t};if(m.c!=null)e.c=m.c;if(m.i!=null)e.i=m.i;if(auto)e.a=1;room.log.push(e);room.at=now;room.v++;}
function finishIfOver(room,g,now){if(!g.over||room.fin)return;
  room.fin={fool:g.fool,pog:g.pogony,lt:g.loserTeam==null?null:g.loserTeam,out:g.out.slice(),at:now};room.st='over';room.dl=0;room.v++;}

// who moves next and when the server should step in for them
function controlled(room,p){const s=room.seats[p];return s.k==='b'||!!s.away||!!s.idle;}
function schedule(room,now,g){
  if(room.st!=='play'){room.dl=0;return;}
  g=g||build(room).g;if(g.over){room.dl=0;return;}
  const tm=g.toMove();
  if(controlled(room,tm)){room.dl=0;return;}
  room.dl=room.opts.timer?room.at+room.opts.timer*1000:0;}
function botDelay(room,g,tm){
  if(room.seats[tm].away||room.seats[tm].idle)return 700;
  // a player who is out of the game watches the rest played out quickly
  if(room.solo&&!g.active(0))return 320;
  const run=lastRun(room,g);
  // give a human attacker time to add a second card before a bot answers
  const more=run>=0&&!controlled(room,run)&&g.hands[run].some(c=>g.canAttack(run,c));
  return 1000+(more?1300:0)+(g.deck.length===0?300:0);}
function safeMove(g,p){
  if(p===g.def&&!g.taking&&g.undefended().length)return {t:'take'};
  if(!g.table.length){const c=g.hands[p].slice().sort((a,b)=>(g.isTrump(a)-g.isTrump(b))||g.rk(a)-g.rk(b)).find(c=>g.canAttack(p,c));return {t:'attack',c:c.id};}
  return {t:'done'};}
function botMove(room,g,p){
  const seat=room.seats[p],solo=!!room.solo&&seat.k==='b';
  // bots look at the table: a wrong card is sometimes called out
  if(g.rules.cheat&&g.cheater()>=0&&g.cheater()!==p&&seat.k==='b'&&Math.random()<.45)return {t:'acc'};
  const st=solo&&typeof charAI==='function'?charAI(seat.ch):seat.k==='b'?STYLES[BOT_STYLE[room.opts.level]]:STYLES.bold;
  const m=aiMove(g,p,st)||g.legal(p).find(x=>x.t==='take'||x.t==='done');
  // a cheating character (Koschei) sometimes lays a wrong card instead
  if(solo&&st.cheat){const c=cheatMove(room,g,p,m);if(c)return c;}
  return {t:m.t,c:m.c?m.c.id:undefined,i:m.i};}
// as defender it covers with a card that does not beat; as a thrower it adds a card of another rank
function cheatMove(room,g,p,m){if(!g.rules.cheat||(room.cc||0)>=4||g.cheater()>=0||!m)return null;const h=g.hands[p];
  if(m.t==='take'&&p===g.def&&Math.random()<.5){const i=g.table.findIndex(x=>!x.d);if(i<0)return null;const a=g.table[i].a;
    const fake=h.filter(c=>c.r!=='J'&&!g.beats(c,a)&&!g.isTrump(c)).sort((x,y)=>(x.s===a.s?-1:1)-(y.s===a.s?-1:1)||g.rk(x)-g.rk(y))[0];
    if(fake){room.cc=(room.cc||0)+1;return {t:'cd',c:fake.id,i};}}
  if(m.t==='done'&&p!==g.def&&Math.random()<.22){const rks=g.ranksOnTable();const extra=h.filter(c=>c.r!=='J'&&!rks.has(c.r)&&!g.isTrump(c)).sort((x,y)=>g.rk(x)-g.rk(y))[0];
    if(extra){room.cc=(room.cc||0)+1;return {t:'ca',c:extra.id};}}
  return null;}
// let bots and timers do what is due; called on every request. Returns true if anything moved.
function advance(room,now,rnd){
  // an open table starts when it is full or has waited long enough; one that everybody left closes
  if(room.q&&room.st==='lobby'){
    if(!room.seats.some(s=>s.k==='h')){room.st='closed';room.v++;return true;}
    if(room.qAt&&now>=room.qAt){start(room,null,now,rnd||Math.random);return true;}
    return false;}
  if(room.st!=='play')return false;let moved=false;
  // players silent for a long time are looked after by a bot until they come back
  if(!room.solo)for(const s of room.seats)if(s.k==='h'&&!s.away&&now-(s.seen||0)>45000){s.away=true;room.v++;moved=true;}
  for(let guard=0;guard<60;guard++){
    const {g}=build(room);g._ap=[];if(g.over){finishIfOver(room,g,now);break;}
    const tm=g.toMove();
    if(controlled(room,tm)){
      const due=room.at+botDelay(room,g,tm);if(now<due)break;
      const m=botMove(room,g,tm);
      if(!applyMove(g,tm,m)){const L=g.legal(tm),f=L.find(x=>x.t==='take'||x.t==='done')||L[0];const mm={t:f.t,c:f.c?f.c.id:undefined,i:f.i};applyMove(g,tm,mm);push(room,tm,mm,Math.max(due,room.at),1);}
      else push(room,tm,m,Math.max(due,room.at),1);
      finishIfOver(room,g,now);schedule(room,now,g);moved=true;continue;}
    if(room.dl&&now>=room.dl){const s=room.seats[tm];const m=safeMove(g,tm);applyMove(g,tm,m);push(room,tm,m,room.dl,1);
      s.to=(s.to||0)+1;if(s.to>=2)s.idle=true;finishIfOver(room,g,now);schedule(room,now,g);moved=true;continue;}
    break;}
  return moved;}
// the earliest moment the server has something to do by itself (for the push transport)
function nextDue(room){
  if(room.q&&room.st==='lobby')return room.qAt;
  if(room.st!=='play')return 0;const {g}=build(room);if(g.over)return 0;const tm=g.toMove();
  return controlled(room,tm)?room.at+botDelay(room,g,tm):room.dl;}

/* ---------- what one player is allowed to see ---------- */
function visibleTo(room,g,s,p,c){return p===s||!!room.opts.rules.open||g.over||c===g.trumpCard||g.known[p].has(c.id);}
// log entries from `since`, with only the cards this seat may know
function entriesFor(room,g,meta,s,since){
  const out=[];
  for(let i=Math.max(0,since);i<room.log.length;i++){const e=room.log[i],M=meta[i],x={p:e.p,t:e.t};
    if(e.c!=null)x.c=e.c;if(e.i!=null)x.i=e.i;if(M.ap.length)x.ap=M.ap;
    const dr=[];let any=false;
    for(let k=M.e0;k<M.e1;k++){const ev=g.events[k];if(ev.t!=='draw')continue;
      // a card drawn is known to its owner (and to all when cards are played open)
      const vis=ev.p===s||room.opts.rules.open||ev.c===g.trumpCard;dr.push(vis?ev.c.id:0);if(vis)any=true;}
    if(dr.length)x.dr=any?dr:dr.length;
    if(i===room.log.length-1&&g.over){x.hs=g.hands.map(h=>h.map(c=>c.id));x.fo=[g.fool,g.pogony,g.loserTeam==null?null:g.loserTeam];}
    out.push(x);}
  return out;}
// the whole table as this seat sees it (joining, coming back, or falling out of step)
function snapshotFor(room,g,s){
  const hide=(p,c)=>visibleTo(room,g,s,p,c)?c.id:0;
  return {n:g.n,mode:g.mode,deck:g.deckSize,rules:room.opts.rules,teams:g.teams,trumpCard:g.trumpCard.id,deckLeft:g.deck.length,
    hands:g.hands.map((h,p)=>h.map(c=>hide(p,c))),table:g.table.map(x=>({a:x.a.id,d:x.d?x.d.id:null})),discard:g.discard.map(c=>c.id),
    out:g.out.slice(),att:g.att,def:g.def,taking:!!g.taking,passed:[...g.passed],shown:[...(g.shown||[])],firstBout:g.firstBout,bouts:g.bouts,limit:g.limit,
    over:g.over,fool:g.fool,pogony:g.pogony,loserTeam:g.loserTeam==null?null:g.loserTeam,cheat:g.table.map(x=>x.cheat!=null?x.cheat:-1),
    chest:room.chest>=0&&room.chest<g.deck.length?room.chest:-1,logLen:room.log.length};}
function lobbyFor(room,s){
  return {code:room.code,v:room.v,st:room.st,game:room.game,host:room.host,me:s,opts:room.opts,dl:room.dl,q:room.q||undefined,qAt:room.q?room.qAt:undefined,solo:room.solo||undefined,
    seats:room.seats.map((x,i)=>({k:x.k,nm:x.k==='h'?x.nm:undefined,ch:x.ch,away:!!(x.away||x.idle),on:x.k==='h'&&!x.away})),
    fin:room.fin};}
// everything a client needs after `since` (log index) and `cs` (chat index); since<0 asks for a snapshot
function viewFor(room,s,since,cs){
  const res={room:lobbyFor(room,s),chat:room.chat.filter(c=>c.i>(cs||0))};
  if(room.st==='lobby')return res;
  const {g,meta}=build(room);
  if(since==null||since<0||since>room.log.length)res.snap=snapshotFor(room,g,s);
  else res.log=entriesFor(room,g,meta,s,since);
  res.logLen=room.log.length;res.chest=room.chest;
  return res;}
function say(room,tok,k,now){const p=seatOf(room,tok);if(p<0)return 'not seated';k=+k;if(!(k>=0&&k<PHRASES.length))return 'bad phrase';
  const last=room.chat[room.chat.length-1];if(last&&last.p===p&&now-last.t<1200)return 'too fast';
  room.chat.push({i:++room.ci,p,k,t:now});if(room.chat.length>20)room.chat.shift();room.seats[p].seen=now;room.v++;return null;}
function leave(room,tok,now){const p=seatOf(room,tok);if(p<0)return 'not seated';
  if(room.st==='lobby'){if(p===room.host){const other=room.seats.findIndex((x,i)=>x.k==='h'&&i!==p);room.seats[p]={k:'o'};if(other>=0)room.host=other;else room.st='closed';}
    else room.seats[p]={k:'o'};}
  else room.seats[p].away=true,room.seats[p].left=1;
  room.v++;return null;}


;
// Open tables for anyone: tables by stake, payouts from the pot, rating and the weekly table.
// Coins stay with the player (in the platform's save); the server says who won how much and keeps the rating.

const QUICK_WAIT=12000; // a table waits this long for people, then bots take the free seats
const RAKE=0.10;        // the table keeps a tenth of the pot, so coins do not pile up forever
const TIERS=[
  {id:'fair', nm:'Ярмарка',    stake:100,   need:0,    level:'easy',   mult:1},
  {id:'merch',nm:'Купеческий', stake:1000,  need:500,  level:'medium', mult:1.5},
  {id:'boyar',nm:'Боярский',   stake:10000, need:1200, level:'hard',   mult:2},
  {id:'tsar', nm:'Царский',    stake:50000, need:2600, level:'hard',   mult:3}];
const TITLES=[[0,'Новичок'],[100,'Подмастерье'],[250,'Мастер'],[500,'Купец'],[800,'Гость торговый'],[1200,'Боярин'],[1800,'Воевода'],[2600,'Князь'],[3600,'Великий князь'],[5000,'Царь']];
const PLACE_PTS={2:[20],3:[20,8],4:[20,10,5]},FOOL_PTS=-12,DRAW_PTS=3;
const SHARE={2:[1],3:[.6,.4],4:[.5,.3,.2]};

function tierOf(id){return TIERS.find(t=>t.id===id)||null;}
function rankOf(r){let x=TITLES[0];for(const k of TITLES)if(r>=k[0])x=k;return x[1];}
function nextRank(r){for(const k of TITLES)if(r<k[0])return {at:k[0],nm:k[1]};return null;}
function weekOf(now){return Math.floor((now+3*3600e3-4*86400e3)/604800e3);} // weeks start on Monday, Moscow time
function quickKey(tier,mode,n){return tier+'|'+mode+'|'+n;}
function quickOpts(t,mode,n){return {deck:36,n:Math.max(2,Math.min(4,+n||2)),mode:mode==='perevodnoy'?'perevodnoy':'podkidnoy',rules:{},timer:30,level:t.level};}
// a table a player sets up in the list: the deck and special rules are theirs (no pairs: the stake is paid by one fool)
const TABLE_RULES=['neighbors','show','noLimit','cheat','dark','fog'];
function tableOpts(t,req){const deck=[24,36,52].includes(+req.deck)?+req.deck:36,n=Math.max(2,Math.min(4,+req.n||2)),mode=req.mode==='perevodnoy'?'perevodnoy':'podkidnoy';
  const R=req.rules||{},rules={};for(const k of TABLE_RULES)if(R[k])rules[k]=true;
  if(n<3)delete rules.neighbors;if(mode!=='perevodnoy')delete rules.show;
  return {deck,n,mode,rules,timer:30,level:t.level};}

// who gets what when a quick game ends: only the fool loses the stake; the others get it back plus a share of the rest
function quickResult(room,fin){
  const n=room.seats.length,S=room.q.stake,t=tierOf(room.q.tier)||TIERS[0];
  const pay=Array(n).fill(0),pts=Array(n).fill(0),place=Array(n).fill(-1);
  if(fin.fool<0){for(let i=0;i<n;i++){pay[i]=S;pts[i]=DRAW_PTS;}return {pay,pts,place};}
  const order=fin.out.filter(p=>p!==fin.fool);for(let i=0;i<n;i++)if(i!==fin.fool&&!order.includes(i))order.push(i);
  const extra=Math.floor(n*S*(1-RAKE))-(n-1)*S,w=SHARE[n]||SHARE[4];
  order.forEach((p,k)=>{place[p]=k;pay[p]=S+Math.floor(extra*(w[k]||0));pts[p]=Math.round(((PLACE_PTS[n]||PLACE_PTS[4])[k]||0)*t.mult);});
  place[fin.fool]=n-1;pts[fin.fool]=Math.round(FOOL_PTS*t.mult);
  return {pay,pts,place};}

/* ---------- accounts: a private id the game makes up for itself, kept by the player ---------- */
function cleanAcct(a){a=String(a||'');return /^[a-z0-9]{16,40}$/.test(a)?a:'';}
function accGet(store,a,now){let x=store.acc.get(a);if(!x){x={nm:'Игрок',r:0,g:0,w:0,wk:weekOf(now),wp:0,t:now};}
  if(x.wk!==weekOf(now)){x.wk=weekOf(now);x.wp=0;}return x;}
function accPut(store,a,x){store.acc.set(a,x);if(store.accDirty)store.accDirty();}
function profile(x){const nx=nextRank(x.r);return {r:x.r,rank:rankOf(x.r),ri:TITLES.findIndex(k=>k[1]===rankOf(x.r)),next:nx,g:x.g,w:x.w,wp:x.wp};}
// applied once per finished quick game
function rateQuick(store,room,now){
  if(!room.q||!room.fin||room.fin.rated)return false;
  const res=quickResult(room,room.fin);room.fin.pay=res.pay;room.fin.pts=res.pts;room.fin.place=res.place;room.fin.rated=1;
  room.seats.forEach((s,i)=>{if(s.k!=='h'||!s.ac)return;const x=accGet(store,s.ac,now);const ri0=TITLES.findIndex(k=>k[1]===rankOf(x.r));
    x.r=Math.max(0,x.r+res.pts[i]);
    // a new rank is worth a notice, and so is a table it opens
    const ri=TITLES.findIndex(k=>k[1]===rankOf(x.r));if(ri>ri0&&typeof note==='function'&&typeof ecoOf==='function'){const open=TIERS.filter(t=>t.need>TITLES[ri0][0]&&t.need<=x.r).map(t=>t.nm);
      note(ecoOf(x),Object.assign({t:'rank',ri,nm:rankOf(x.r)},open.length?{open}:{}),now);}x.g++;if(res.place[i]>=0&&i!==room.fin.fool)x.w++;x.wp+=Math.max(0,res.pts[i]);x.nm=s.nm;x.t=now;accPut(store,s.ac,x);});
  room.v++;return true;}
function topLists(store,now,me){
  const wk=weekOf(now),all=[...store.acc.entries()].filter(([,x])=>x.g>0);
  const week=all.filter(([,x])=>x.wk===wk&&x.wp>0).sort((a,b)=>b[1].wp-a[1].wp);
  const ever=all.slice().sort((a,b)=>b[1].r-a[1].r);
  const row=([a,x])=>({nm:x.nm,r:x.r,wp:x.wp,rank:rankOf(x.r),ri:TITLES.findIndex(k=>k[1]===rankOf(x.r)),lvl:x.eco?x.eco.lvl:1,me:a===me||undefined});
  return {week:week.slice(0,20).map(row),ever:ever.slice(0,20).map(row),
    myWeek:me?week.findIndex(([a])=>a===me)+1:0,myEver:me?ever.findIndex(([a])=>a===me)+1:0};}


;
// The player's belongings, kept on the server: coins, the shop, the road, tasks, gifts, achievements.
// The browser only shows them and asks for changes; every change is checked here.
// Needs rules.js (shop, achievements, tasks) and quick.js (accounts) in scope.

const AD_COINS=60,AD_COINS_DAY=5,BAIL_COINS=500,MIGRATE_MAX=50000;
const ADS_PLAT=new Set(['pikabu','web']); // gift doubling and task swaps for ads: only where the platform pays well for them
const REWARD_PLAT=new Set(['pikabu','web','vk']); // coins for an ad and doubling a win: everywhere with rewarded ads (VK and OK too)

function ecoOf(x){if(!x.eco){x.eco=freshEco();}return x.eco;}
// what the browser gets: everything it needs to draw, nothing secret
function ecoView(x,news){const e=ecoOf(x),o={};for(const k of ECO_KEYS)if(e[k]!==undefined)o[k]=e[k];
  return {eco:o,me:profile(x),news:news||[]};}
// the player's notices: new levels and ranks, achievements, purchases, stakes given back; the newest 30 are kept
const INBOX_MAX=30;
function note(e,n,now){if(!e.inbox)e.inbox=[];e.nid=(e.nid||0)+1;e.inbox.push(Object.assign({id:e.nid,at:now||Date.now()},n));
  if(e.inbox.length>INBOX_MAX)e.inbox.splice(0,e.inbox.length-INBOX_MAX);}
function addXp(e,n,news){if(!e.lvl)e.lvl=1;e.xp=(e.xp||0)+n;
  while(e.xp>=xpFor(e.lvl+1)){e.lvl++;const c=LEVEL_COINS(e.lvl);gain(e,c);news.push({t:'lvl',lvl:e.lvl,c});note(e,{t:'lvl',lvl:e.lvl,c});}}
function gain(e,n){e.coins+=n;e.st.coinsEarned=(e.st.coinsEarned||0)+Math.max(0,n);}
function own(e,id){if(!e.owned.includes(id))e.owned.push(id);}
// achievements are checked after every change and paid at once
function payAch(e,news,now){for(const a of achDue(e)){e.ach[a.id]=now;gain(e,a.c);news.push({t:'ach',name:a.name,d:a.d,c:a.c});note(e,{t:'ach',name:a.name,d:a.d,c:a.c},now);}}

// a player who played before this version brings the save from the browser once; it is taken within reason
function migrate(e,old){if(!old||typeof old!=='object'||old.v!==2)return;
  e.coins=Math.max(0,Math.min(MIGRATE_MAX,Math.floor(+old.coins||0)));
  if(Array.isArray(old.owned))for(const id of old.owned)if(shopItem(id))own(e,id);
  for(const k of ['back','face','tableSkin'])if(typeof old[k]==='string'&&e.owned.includes(old[k]))e[k]=old[k];
  if(old.camp&&typeof old.camp==='object')for(const k in old.camp){const r=old.camp[k];const [l,i]=k.split('.');const L=LOCS.find(x=>x.id===l);
    if(L&&L.stages[+i]&&r&&Array.isArray(r.stars))e.camp[k]={won:!!r.won,stars:r.stars.slice(0,3).map(v=>v?1:0)};}
  if(old.st&&typeof old.st==='object')for(const k in e.st){const v=old.st[k];if(typeof v==='number'&&typeof e.st[k]==='number')e.st[k]=Math.max(0,Math.min(1e6,Math.floor(v)));
    else if(v&&typeof v==='object'&&typeof e.st[k]==='object')e.st[k]=JSON.parse(JSON.stringify(v));}
  if(old.ach&&typeof old.ach==='object')for(const a of ACH)if(old.ach[a.id])e.ach[a.id]=+old.ach[a.id]||1;
  if(old.gift&&typeof old.gift.day==='string')e.gift={day:old.gift.day,streak:Math.max(0,Math.min(GIFTS.length,+old.gift.streak||0))};
  if(old.daily&&typeof old.daily.day==='string')e.daily={day:old.daily.day,done:!!old.daily.done};}

// one request about belongings; returns the new state, or an error and the state as it is
function ecoOp(store,ac,req,now){
  const x=accGet(store,ac,now),e=ecoOf(x),news=[],today=dayOf(now),op=req.op,plat=/^(vk|ok)user/.test(ac)?'vk':String(req.plat||'web');
  let err=null,res={};
  if(op==='prof'){if(!x.migrated){x.migrated=1;migrate(e,req.mig);}}
  else if(op==='buy'){const it=shopItem(String(req.id));
    if(!it||it.price<=0)err='not for sale';else if(e.owned.includes(it.id))err='owned';else if(e.coins<it.price)err='coins';
    else{e.coins-=it.price;own(e,it.id);e[{backs:'back',faces:'face',tables:'tableSkin'}[it.kind]]=it.id;}}
  else if(op==='equip'){const it=shopItem(String(req.id));
    if(!it||!e.owned.includes(it.id))err='not owned';else e[{backs:'back',faces:'face',tables:'tableSkin'}[it.kind]]=it.id;}
  else if(op==='gift'){if(e.gift.day===today)err='taken';
    else{const streak=e.gift.day===prevDayOf(now)?Math.min(e.gift.streak+1,GIFTS.length):1,amount=GIFTS[streak-1];
      e.gift={day:today,streak};gain(e,amount);res.amount=amount;}}
  else if(op==='giftx2'){if(!ADS_PLAT.has(plat))err='no ads';else if(e.gift.day!==today||e.gift.dbl===today)err='no gift';
    else{const amount=GIFTS[e.gift.streak-1]||0;e.gift.dbl=today;gain(e,amount);res.amount=amount;}}
  else if(op==='adcoins'){if(!REWARD_PLAT.has(plat))err='no ads';else{if(!e.adCoins||e.adCoins.d!==today)e.adCoins={d:today,n:0};
    if(e.adCoins.n>=AD_COINS_DAY)err='limit';else{e.adCoins.n++;gain(e,AD_COINS);res.amount=AD_COINS;}}}
  else if(op==='dalt'){if(!ADS_PLAT.has(plat))err='no ads';else if(e.daily&&e.daily.day===today&&e.daily.done)err='done';
    else e.dailyAlt={day:today,n:(e.dailyAlt&&e.dailyAlt.day===today?e.dailyAlt.n:0)+1};}
  else if(op==='bail'){if(e.coins>=100)err='has coins';else if(e.bail===today)err='taken';else{e.bail=today;gain(e,BAIL_COINS);res.amount=BAIL_COINS;}}
  else if(op==='seen'){e.seen=Math.max(e.seen||0,Math.min(Math.floor(+req.id||0),e.nid||0));}
  else err='bad op';
  payAch(e,news,now);x.t=now;accPut(store,ac,x);
  return Object.assign(ecoView(x,news),res,err?{err}:{});}


;
// Games with bots, run on the server: what may be played, and what a finished game brings.
// Needs rules.js, charai.js, room.js, quick.js and eco.js in scope.

// what the player asked to play, checked against what they have opened
function soloSetup(e,req){const k=String(req.kind||'');
  if(k==='camp'){const li=+req.li,si=+req.si,L=LOCS[li];if(!L||!L.stages[si])return {err:'bad stage'};
    const open=(li===0||campRec(e.camp,LOCS[li-1].id,LOCS[li-1].stages.length-1).won)&&(si===0||campRec(e.camp,L.id,si-1).won);
    if(!open)return {err:'locked'};const st=L.stages[si];
    return {opts:{mode:st.mode,deck:st.deck,rules:st.rules||{},level:'medium'},chars:st.opps.slice(),solo:{kind:'camp',li,si,goals:st.goals}};}
  if(k==='daily'){const d=dailyTaskFor(dayOf(Date.now()),e.dailyAlt);
    const pool=levelPool('medium',e.camp),chars=pickFrom(pool,d.players-1);
    return {opts:{mode:d.mode,deck:d.deck,rules:{},level:'medium'},chars,solo:{kind:'daily',goals:['win',d.goal],day:dayOf(Date.now())}};}
  if(k==='quick'){const level=LEVELS[req.level]?req.level:'medium',pool=levelPool(level,e.camp);
    let chars=Array.isArray(req.opps)?req.opps.map(String).filter(c=>pool.includes(c)):[];chars=[...new Set(chars)];
    const deck=[24,36,52,54].includes(+req.deck)?+req.deck:36,max={24:3,36:4,52:5,54:5}[deck],want=Math.max(1,Math.min(max,+req.n||chars.length||1));
    if(chars.length!==want)chars=pickFrom(pool,want);
    return {opts:{mode:req.mode,deck,rules:req.rules||{},level},chars,solo:{kind:'quick',level}};}
  return {err:'bad kind'};}
function pickFrom(pool,k){const a=pool.slice();for(let i=a.length-1;i>0;i--){const j=Math.floor(Math.random()*(i+1));[a[i],a[j]]=[a[j],a[i]];}return a.slice(0,k);}

// everything known about a finished game from the player's side (seat 0)
function soloFacts(room,me){me=me||0;const {g,meta}=build(room),n=g.n,fool=g.fool,team=!!g.teams;
  const win=team?g.loserTeam!==g.teams[me]:fool!==me&&!(n===2&&fool===-1);
  let takes=0,transfers=0,caught=0;
  room.log.forEach((e,i)=>{if(e.p!==me)return;if(e.t==='take')takes++;if(e.t==='transfer'||e.t==='show')transfers++;
    if(e.t==='acc'){const M=meta[i];const ev=g.events.slice(M.e0,M.e1).find(x=>x.t==='accuse');if(ev&&ev.caught)caught++;else if(ev)takes++;}});
  const lastM=meta[meta.length-1],lastOuts=lastM?g.events.slice(lastM.e0,lastM.e1).filter(x=>x.t==='out').map(x=>x.p):[];
  let chest=false;if(room.chest>=0){const g0=new Game(gameOpts(room));const cc=g0.deck[room.chest];chest=!!cc&&g.events.some(x=>x.t==='draw'&&x.p===me&&x.c.id===cc.id);}
  return {win,draw:fool===-1,fool:fool===me?0:fool<0?-1:1,n,firstOut:g.out[0]===me,takes,transfers,bouts:g.bouts,caught,chest,
    pogGiven:g.pogony>0&&fool>=0&&fool!==me&&lastOuts.includes(me)&&(g.lastPlayed[me]||[]).some(c=>c.r==='6'),pogGot:g.pogony>0&&fool===me,
    mode:g.mode,deck:g.deckSize};}
function addStats(e,r){const s=e.st,n=r.n;s.games++;if(r.win)s.wins++;else if(r.fool===0)s.losses++;else s.draws++;
  if(r.win){s.streak++;s.bestStreak=Math.max(s.bestStreak,s.streak);}else if(r.fool===0)s.streak=0;
  if(r.pogGiven)s.pogGiven++;if(r.pogGot)s.pogGot++;if(r.win&&r.takes===0)s.noTakeWins++;if(r.firstOut)s.firstOuts++;
  s.takes+=r.takes;s.transfers+=r.transfers;
  if(r.win&&n>=4)s.bigWins++;if(r.win&&n>=6)s.sixWins++;if(r.win&&r.deck===54)s.win54++;
  const bm=s.byMode[r.mode]||(s.byMode[r.mode]={g:0,w:0}),bd=s.byDeck[r.deck]||(s.byDeck[r.deck]={g:0,w:0}),bp=s.byPlayers[n]||(s.byPlayers[n]={g:0,w:0});bm.g++;bd.g++;bp.g++;if(r.win){bm.w++;bd.w++;bp.w++;}}
function soloLoss(e,o){const s=e.st;s.games++;s.losses++;s.quits=(s.quits||0)+1;s.streak=0;
  const bm=s.byMode[o.mode],bd=s.byDeck[o.deck]||(s.byDeck[o.deck]={g:0,w:0}),bp=s.byPlayers[o.n]||(s.byPlayers[o.n]={g:0,w:0});if(bm)bm.g++;bd.g++;bp.g++;}
// counts as played once a card was on the table
function soloCounts(room){if(room.st!=='play')return false;const {g}=build(room);return !g.over&&(g.bouts>0||g.table.length>0);}

// a finished game with bots: statistics, the road's stars, the task of the day, coins
function settleSolo(store,room,now){
  if(!room.solo||!room.fin||room.fin.res)return false;const s=room.seats[0];if(!s.ac)return false;
  const x=accGet(store,s.ac,now),e=ecoOf(x),r=soloFacts(room),S=room.solo,rw=[],news=[];let coins=0,stars=null;
  addStats(e,r);
  if(S.kind==='camp'){const L=LOCS[S.li],st=L.stages[S.si],key=L.id+'.'+S.si,prev=campRec(e.camp,L.id,S.si);
    const got=st.goals.map(k=>goalMet(k,r)?1:0),all=prev.stars.map((v,i)=>v||got[i]),fresh=all.reduce((a,b)=>a+b,0)-prev.stars.reduce((a,b)=>a+b,0);
    if(r.win)coins+=stageReward(S.li,S.si,prev);coins+=fresh*10;e.camp[key]={won:prev.won||r.win,stars:all};stars=got;
    if(fresh>0)rw.push('★ +'+fresh);
    if(r.win&&!prev.won){if(L.id==='palace'&&S.si===2&&!e.owned.includes('palaty')){own(e,'palaty');rw.push('Стол «Царские палаты»');}
      if(L.id==='palace'&&S.si===3&&!e.owned.includes('tsar')){own(e,'tsar');rw.push('Рубашка «Царская»');}}
    if(campStars(e.camp)>=STARS_MAX&&!e.owned.includes('gold')){own(e,'gold');rw.push('Колода «Золотая»');}}
  else if(S.kind==='quick'){if(r.win)coins+=quickReward(r.n-1,S.level)+(r.pogGiven?10:0);else if(r.draw)coins+=5;}
  else if(S.kind==='daily'){const got=S.goals.map(k=>goalMet(k,r)?1:0);stars=got;const done=e.daily&&e.daily.day===S.day&&e.daily.done;
    if(got.every(Boolean)&&!done&&S.day===dayOf(now)){e.daily={day:S.day,done:true};coins+=DAILY_REWARD;rw.push('Задание дня выполнено');
      e.st.dailyCount=(e.st.dailyCount||0)+1;if(e.st.dailyCount>=7&&!e.owned.includes('morozko')){own(e,'morozko');rw.push('Стол «Морозко»');}}
    else if(!done)rw.push('Задание дня не выполнено — попробуйте ещё');}
  if(r.chest){coins+=CHEST_COINS;rw.push('Клад +'+CHEST_COINS);}
  if(r.caught){coins+=r.caught*CAUGHT_COINS;rw.push('Пойман шулер ×'+r.caught+': +'+r.caught*CAUGHT_COINS);}
  if(coins&&r.win&&e.iap&&e.iap.boyar){coins*=2;rw.push('Боярский пакет: монеты ×2');}
  if(coins){gain(e,coins);rw.unshift('+'+coins+' монет');}
  const xp=10+(r.win?15:0);addXp(e,xp,news);rw.push('Опыт +'+xp);
  e.lastWin=r.win&&coins>0?{code:room.code,amount:coins}:null;
  if(e.live&&e.live.code===room.code)e.live=null;
  payAch(e,news,now);x.t=now;accPut(store,s.ac,x);
  room.fin.res={coins,rw,stars,r,news,eco:ecoView(x).eco};room.v++;return true;}

// start a game with bots; an unfinished earlier one counts as lost
async function soloStart(store,req,ac,now){
  const x=accGet(store,ac,now),e=ecoOf(x),set=soloSetup(e,req);if(set.err)return {err:set.err};
  if(e.live){const old=await store.load(e.live.code);if(old&&old.room.st==='play'&&soloCounts(old.room))soloLoss(e,e.live);if(old&&old.room.st==='play'){old.room.st='closed';old.room.v++;await store.save(old.room,old.ver);}e.live=null;}
  for(let k=0;k<6;k++){const r=newSolo(set.opts,set.chars,set.solo,req.name,now,rndSecure,ac);
    if(await store.create(r.room)){e.live={code:r.room.code,mode:r.room.opts.mode,deck:r.room.opts.deck,n:r.room.opts.n};accPut(store,ac,x);
      return Object.assign({tok:r.tok,seat:0},viewFor(r.room,0,-1,0),{now,due:nextDue(r.room)});}}
  return {err:'busy'};}
// leaving an unfinished game with bots: a loss, and the table closes
function soloLeave(store,room,now){if(!room.solo)return;const s=room.seats[0];if(!s.ac)return;const x=accGet(store,s.ac,now),e=ecoOf(x);
  if(soloCounts(room))soloLoss(e,{mode:room.opts.mode,deck:room.opts.deck,n:room.opts.n});
  if(e.live&&e.live.code===room.code)e.live=null;room.st='closed';room.v++;accPut(store,s.ac,x);}
// doubling the coins of the last win for an ad (where there are ads)
function winDouble(store,ac,req,now){const x=accGet(store,ac,now),e=ecoOf(x),news=[];
  if(!REWARD_PLAT.has(/^(vk|ok)user/.test(ac)?'vk':String(req.plat||'web')))return Object.assign(ecoView(x),{err:'no ads'});
  if(!e.lastWin||e.lastWin.code!==req.code)return Object.assign(ecoView(x),{err:'no win'});
  const a=e.lastWin.amount;e.lastWin=null;gain(e,a);payAch(e,news,now);accPut(store,ac,x);return Object.assign(ecoView(x,news),{amount:a});}

// a finished game with people (friends' table or an open table): statistics and coins for every person at it
const FRIEND_WIN=30,FRIEND_WINS_DAY=5;
function settleNet(store,room,now){
  if(room.solo||!room.fin||room.fin.seatRes)return false;const out=[];
  room.seats.forEach((s,i)=>{if(s.k!=='h'||!s.ac){out.push(null);return;}
    const x=accGet(store,s.ac,now),e=ecoOf(x),r=soloFacts(room,i),rw=[],news=[];let coins=0;addStats(e,r);
    if(room.q){const pay=(room.fin.pay||[])[i]||0,pts=(room.fin.pts||[])[i]||0;coins+=pay;
      if(!pay)rw.push('Ставка '+room.q.stake+' проиграна');if(pts)rw.push('Рейтинг '+(pts>0?'+':'')+pts);}
    else if(r.win&&room.seats.filter(z=>z.k==='h').length>=2){const d=dayOf(now);if(!e.netDay||e.netDay.d!==d)e.netDay={d,w:0};
      if(e.netDay.w<FRIEND_WINS_DAY){e.netDay.w++;coins+=FRIEND_WIN;}else rw.push('Монеты за победы над друзьями — до 5 раз в день');}
    if(r.win&&!e.owned.includes('skaz')){own(e,'skaz');rw.push('Колода «Сказочная»');}
    if(r.chest){coins+=CHEST_COINS;rw.push('Клад +'+CHEST_COINS);}
    if(r.caught){coins+=r.caught*CAUGHT_COINS;rw.push('Пойман шулер ×'+r.caught+': +'+r.caught*CAUGHT_COINS);}
    if(coins){gain(e,coins);rw.unshift('+'+coins+' монет');}
    const xp=15+(r.win?20:0);addXp(e,xp,news);rw.push('Опыт +'+xp);
    payAch(e,news,now);accPut(store,s.ac,x);out.push({coins,rw,news});});
  room.fin.seatRes=out;room.v++;return true;}
// a seat at an open table costs the stake at once; leaving before the start gives it back
function stakeTake(store,ac,stake,now){const x=accGet(store,ac,now),e=ecoOf(x);if(e.coins<stake)return false;e.coins-=stake;accPut(store,ac,x);return true;}
function stakeBack(store,ac,stake,now){const x=accGet(store,ac,now),e=ecoOf(x);e.coins+=stake;accPut(store,ac,x);}


;
// Real-money purchases and platform accounts, checked on the server.
// Secrets come from the machine's metadata (see vm.js): {pikabu:"…" or ["…"], vk:"…", ok:"…", allowTest:true}.
// Needs eco.js and quick.js in scope.
const crypto_=typeof require==='function'?require('crypto'):null;

const IAP_COINS={coins3000:3000,coins10000:10000,coins30000:30000,coins100000:100000};
const IAP_IDS=new Set(['noads','starter','boyar','coins3000','coins10000','coins30000','coins100000']);
// what a product gives; permanent ones once, coin packs once per purchase
function iapGrant(e,id,pid){if(!IAP_IDS.has(id))return false;if(!e.iapDone)e.iapDone={};if(!e.iap)e.iap={};
  if(pid&&e.iapDone[pid])return false;
  if(IAP_COINS[id]){if(pid)e.iapDone[pid]=1;gain(e,IAP_COINS[id]);return true;}
  if(pid)e.iapDone[pid]=1;if(e.iap[id])return false;e.iap[id]=true;
  if(id==='starter'){gain(e,2000);own(e,'gorodets');own(e,'russ');}
  if(id==='boyar'){own(e,'boyar');e.iap.noads=true;}
  if(id==='noads')e.iap.noads=true;
  return true;}
function iapNote(e,id){if(typeof note==='function')note(e,{t:'buy',name:VK_PRICES[id]?VK_PRICES[id].t:id});}

/* ---------- Pikabu: a purchase comes as a JWT signed (HS256) with the game's secret key ---------- */
const b64url=buf=>buf.toString('base64').replace(/=+$/,'').replace(/\+/g,'-').replace(/\//g,'_');
function jwtCheck(token,secret){const parts=String(token||'').split('.');if(parts.length!==3)return null;
  try{const head=JSON.parse(Buffer.from(parts[0],'base64url').toString('utf8'));if(head.alg!=='HS256')return null;
    const want=Buffer.from(b64url(crypto_.createHmac('sha256',secret).update(parts[0]+'.'+parts[1]).digest())),got=Buffer.from(parts[2]);
    if(want.length!==got.length||!crypto_.timingSafeEqual(want,got))return null;
    return JSON.parse(Buffer.from(parts[1],'base64url').toString('utf8'));}catch(e){return null;}}
function pikabuPurchase(secrets,sd){const keys=[].concat(secrets.pikabu||[]).filter(Boolean);
  for(const k of keys){const d=jwtCheck(sd,k);if(d&&d.productId)return d;}return null;}
// the player shows a signed purchase; a purchase is used by one account only
function iapClaim(store,ac,req,now){const x=accGet(store,ac,now),e=ecoOf(x),S=store.secrets||{},news=[];
  if(!store.iapUsed)store.iapUsed=new Map();
  const d=pikabuPurchase(S,req.sd);if(!d)return Object.assign(ecoView(x),{err:S.pikabu?'bad purchase':'not configured'});
  if(d.isTestPurchase&&!S.allowTest)return Object.assign(ecoView(x),{err:'test purchase'});
  const pid='pk:'+String(d.purchaseId||'');const owner=store.iapUsed.get(pid);
  if(owner&&owner!==ac)return Object.assign(ecoView(x),{err:'used'});
  store.iapUsed.set(pid,ac);if(store.accDirty)store.accDirty();
  const given=iapGrant(e,String(d.productId),pid);if(given)iapNote(e,String(d.productId));payAch(e,news,now);accPut(store,ac,x);
  return Object.assign(ecoView(x,news),{given,productId:d.productId,consumable:!!IAP_COINS[d.productId]});}

/* ---------- VK and OK: who the player is, from the signed launch parameters ---------- */
// sign = base64url(HMAC-SHA256(secret, the vk_* parameters sorted and joined as a query string))
function vkUser(secrets,lp){if(!secrets.vk||!lp)return null;let q;try{q=new URLSearchParams(String(lp));}catch(e){return null;}
  const keys=[...q.keys()].filter(k=>k.startsWith('vk_')).sort();if(!keys.length)return null;
  const str=keys.map(k=>k+'='+encodeURIComponent(q.get(k))).join('&');
  const want=b64url(crypto_.createHmac('sha256',secrets.vk).update(str).digest()),got=String(q.get('sign')||'');
  if(!got||want.length!==got.length||!crypto_.timingSafeEqual(Buffer.from(want),Buffer.from(got)))return null;
  const uid=q.get('vk_user_id');if(!/^\d+$/.test(uid||''))return null;
  return {uid,ok:q.get('vk_client')==='ok'};}
const platAcct=(uid,ok)=>(ok?'okuser':'vkuser')+uid.padStart(12,'0');
// the account a request speaks for: in VK/OK the signed user, elsewhere the game's own private id
function resolveAcct(store,req){
  // until the VK key is in the machine's metadata, players are known by the game's own id, as everywhere
  if(req.lp&&(store.secrets||{}).vk){const u=vkUser(store.secrets,req.lp);return u?platAcct(u.uid,u.ok):'';}
  const a=cleanAcct(req.acct);return /^(vk|ok)user/.test(a)?'':a;}

/* ---------- payment notifications from VK (POST, form) and OK (GET) ---------- */
const VK_PRICES={noads:{t:'Без рекламы',vk:35,ok:249},starter:{t:'Стартовый набор',vk:21,ok:149},boyar:{t:'Боярский пакет',vk:57,ok:399},
  coins3000:{t:'Мешок монет',vk:14,ok:99},coins10000:{t:'Царская казна',vk:35,ok:249},coins30000:{t:'Сундук золота',vk:79,ok:549},coins100000:{t:'Царская сокровищница',vk:199,ok:1390}};
const VK_PHOTO='https://ttgms.github.io/durak/vk/item.jpg';
const md5=s=>crypto_.createHash('md5').update(s,'utf8').digest('hex');
const sigOf=(p,secret)=>md5(Object.keys(p).filter(k=>k!=='sig').sort().map(k=>k+'='+p[k]).join('')+secret);
const sameHex=(a,b)=>typeof a==='string'&&typeof b==='string'&&a.length===b.length&&crypto_.timingSafeEqual(Buffer.from(a.toLowerCase()),Buffer.from(b.toLowerCase()));
function vkErr(code,msg,critical){return {error:{error_code:code,error_msg:msg,critical:!!critical}};}
function vkNotify(store,p,now){const secret=(store.secrets||{}).vk;if(!secret)return vkErr(2,'not configured',false);
  if(!sameHex(sigOf(p,secret),p.sig))return vkErr(10,'bad signature',true);
  const type=String(p.notification_type||''),it=VK_PRICES[p.item],ok=/ok/i.test(String(p.site||''));
  if(type.startsWith('get_item')){if(!it)return vkErr(20,'no such item',true);
    return {response:{item_id:p.item,title:it.t,photo_url:VK_PHOTO,price:ok?it.ok:it.vk,expiration:3600}};}
  if(type.startsWith('order_status_change')){
    if(p.status!=='chargeable')return {response:{order_id:Number(p.order_id),app_order_id:Number(p.order_id)}};
    const item=p.item||p.item_id;if(!VK_PRICES[item]||!/^\d+$/.test(String(p.user_id||'')))return vkErr(11,'bad order',true);
    const ac=platAcct(String(p.user_id),ok),x=accGet(store,ac,now),e=ecoOf(x),news=[];
    if(iapGrant(e,item,'vk:'+p.order_id))iapNote(e,item);payAch(e,news,now);accPut(store,ac,x);
    return {response:{order_id:Number(p.order_id),app_order_id:Number(p.order_id)}};}
  return vkErr(11,'unknown notification',true);}
function okNotify(store,q,now){const S=store.secrets||{},secret=S.ok||S.vk;
  const xmlErr=(c,m)=>({err:true,code:c,body:`<?xml version="1.0" encoding="UTF-8"?><ns2:error_response xmlns:ns2="http://api.forticom.com/1.0/"><error_code>${c}</error_code><error_msg>${m}</error_msg></ns2:error_response>`});
  if(!secret)return xmlErr(9999,'SYSTEM : not configured');
  if(!sameHex(sigOf(q,secret),q.sig))return xmlErr(104,'PARAM_SIGNATURE : bad signature');
  const it=VK_PRICES[q.product_code];if(!it)return xmlErr(1001,'CALLBACK_INVALID_PAYMENT : no such product');
  if(Number(q.amount)!==it.ok)return xmlErr(1001,'CALLBACK_INVALID_PAYMENT : wrong amount');
  if(!/^\d+$/.test(String(q.uid||'')))return xmlErr(1001,'CALLBACK_INVALID_PAYMENT : no user');
  const ac=platAcct(String(q.uid),true),x=accGet(store,ac,now),e=ecoOf(x),news=[];if(iapGrant(e,q.product_code,'ok:'+q.transaction_id))iapNote(e,q.product_code);payAch(e,news,now);accPut(store,ac,x);
  return {err:false,body:'<?xml version="1.0" encoding="UTF-8"?><callbacks_payment_response xmlns="http://api.forticom.com/1.0/">true</callbacks_payment_response>'};}


;
// Request handling for the friends' table, independent of where rooms are stored and how messages travel.
// store: {load(code) -> {room,ver}|null, save(room,ver) -> bool (false if someone changed it meanwhile), create(room) -> bool}
// Every change is: load, change, save-if-unchanged; on a clash the whole step is simply repeated.

function rndSecure(){try{const b=require('crypto').randomBytes(4);return b.readUInt32LE(0)/4294967296;}catch(e){return Math.random();}}
const ECO_OPS=new Set(['seen','prof','buy','equip','gift','giftx2','adcoins','dalt','bail']);
const OPS=new Set(['create','join','poll','act','cfg','start','say','leave','tick','quick','me','top','solo','winx2','iap','tables','tcreate','tjoin','sweep',...ECO_OPS]);
/* ---------- the list of open tables and who is online ---------- */
// what the list shows of each table that waits for players or is being played; kept up to date on every change
const TABLES=new Map();let tablesReady=false;
const SEEN=new Map(); // account -> last request: "online" is everyone heard from in the last minute and a half
const ONLINE_MS=90000,STALE_MS=75000;
function track(store,room,now){if(!room||!room.q)return;
  if(room.st!=='lobby'&&room.st!=='play'){TABLES.delete(room.code);return;}
  let seen=0;const seats=room.seats.map(s=>{if(s.k!=='h')return {k:s.k};seen=Math.max(seen,s.seen||0);
    const x=s.ac?store.acc.get(s.ac):null;return {k:'h',nm:s.nm,ri:x?profile(x).ri:0,lvl:x&&x.eco?x.eco.lvl:1};});
  TABLES.set(room.code,{code:room.code,tier:room.q.tier,stake:room.q.stake,list:!!room.q.list,deck:room.opts.deck,n:room.opts.n,mode:room.opts.mode,rules:room.opts.rules,
    st:room.st,host:room.host,seats,seen,born:room.born});}
function tablesInit(store){if(tablesReady)return;tablesReady=true;if(!store._m)return;
  for(const [,rec] of store._m){try{const r=JSON.parse(rec.d);if(r.q&&(r.st==='lobby'||r.st==='play'))track(store,r,Date.now());}catch(e){}}}
function onlineCount(now){let n=0;for(const t of SEEN.values())if(now-t<ONLINE_MS)n++;return n;}
function tableList(store,ac,now){tablesInit(store);const out=[];let playing=0;
  for(const t of TABLES.values()){if(t.st==='play'){playing++;}
    else if(now-t.seen>STALE_MS||!t.seats.some(s=>s.k==='o'))continue;
    out.push(t);}
  // waiting tables first (the fullest on top), then the ones being played
  out.sort((a,b)=>(a.st==='play')-(b.st==='play')||b.seats.filter(s=>s.k==='h').length-a.seats.filter(s=>s.k==='h').length||b.born-a.born);
  return {tables:out.slice(0,60),online:Math.max(onlineCount(now),ac?1:0),playing,now};}
// tables everybody walked away from before the start close, and the stakes go back
async function sweep(store,now){tablesInit(store);
  for(const [a,t] of SEEN)if(now-t>ONLINE_MS*4)SEEN.delete(a);
  for(const t of [...TABLES.values()]){if(t.st!=='lobby'||now-t.seen<STALE_MS+15000)continue;
    for(let attempt=0;attempt<3;attempt++){const rec=await store.load(t.code);if(!rec||rec.room.st!=='lobby'){TABLES.delete(t.code);break;}
      const room=rec.room;if(room.seats.some(s=>s.k==='h'&&now-(s.seen||0)<STALE_MS)){track(store,room,now);break;}
      const back=room.seats.filter(s=>s.k==='h'&&s.ac&&s.paid).map(s=>[s.ac,s.paid]);
      room.st='closed';room.v++;if(!(await store.save(room,rec.ver)))continue;
      for(const [a,p] of back){stakeBack(store,a,p,now);const x=accGet(store,a,now);note(ecoOf(x),{t:'refund',c:p},now);accPut(store,a,x);}if(room.q.key)openDrop(room.q.key,room.code);TABLES.delete(t.code);break;}}
  return {ok:1};}
// open tables that still wait for people, by kind (tier|mode|players); only a hint, every table is checked on load
const OPEN=new Map();
function openAdd(key,code){if(!OPEN.has(key))OPEN.set(key,[]);OPEN.get(key).push(code);}
function openDrop(key,code){const a=OPEN.get(key);if(!a)return;const i=a.indexOf(code);if(i>=0)a.splice(i,1);}

async function handle(store,req,now){
  now=now||Date.now();const op=String(req.op||'');
  if(!OPS.has(op))return {err:'bad op'};
  if(!store.acc)store.acc=new Map();
  const ac=resolveAcct(store,req);if(ac)SEEN.set(ac,now);
  if(op==='sweep')return req._internal?sweep(store,now):{err:'bad op'};
  if(op==='tables')return tableList(store,ac,now);
  if(op==='tcreate')return tableCreate(store,req,ac,now);
  if(op==='tjoin')return tableJoin(store,req,ac,now);
  if(op==='me'){if(!ac)return {err:'bad acct'};const x=accGet(store,ac,now);return {me:profile(x),tiers:TIERS,now};}
  if(op==='top')return Object.assign(topLists(store,now,ac),{now});
  if(op==='quick')return quickJoin(store,req,ac,now);
  if(op==='solo'){if(!ac)return {err:'bad acct'};return soloStart(store,req,ac,now);}
  if(op==='iap'){if(!ac)return {err:'bad acct'};return Object.assign(iapClaim(store,ac,req,now),{now});}
  if(op==='winx2'){if(!ac)return {err:'bad acct'};return Object.assign(winDouble(store,ac,req,now),{now});}
  if(ECO_OPS.has(op)){if(!ac)return {err:'bad acct'};return Object.assign(ecoOp(store,ac,req,now),{now});}
  if(op==='create'){
    for(let k=0;k<8;k++){const r=newRoom(req.opts,req.name,now,rndSecure,ac);
      if(await store.create(r.room))return Object.assign({tok:r.tok,seat:0},viewFor(r.room,0,-1,0),{now});}
    return {err:'busy'};}
  const code=normCode(req.code);if(!code)return {err:'bad code'};
  for(let attempt=0;attempt<6;attempt++){
    const rec=await store.load(code);if(!rec||rec.room.st==='closed'||rec.room.exp<now)return {err:'no room'};
    const room=rec.room,v0=room.v,l0=room.log.length,c0=room.ci;let err=null,seat=seatOf(room,req.tok),tok=req.tok;
    if(op==='tick'){advance(room,now,rndSecure);rateQuick(store,room,now);settleSolo(store,room,now);settleNet(store,room,now);if(room.q&&room.st!=='lobby')openDrop(room.q.key,room.code);
      if(room.v!==v0&&!(await store.save(room,rec.ver)))continue;track(store,room,now);return {room:{code:room.code},due:nextDue(room),_l0:l0,_c0:c0,now};}
    // a seat at a table with a stake is only taken through the list or the quick game, where the stake is paid
    if(op==='join'&&room.q&&seatOf(room,req.tok)<0)return {err:'quick'};
    if(op==='join'){const r=join(room,req.name,now,rndSecure,req.tok,ac);if(r.err)return {err:r.err};seat=r.seat;tok=r.tok;}
    else{if(seat<0)return {err:'not seated'};const s=room.seats[seat];
      if(now-(s.seen||0)>15000||(s.away&&!s.left)){s.seen=now;s.away=false;room.v++;}}
    if(op==='act')err=act(room,tok,req.m||{},now);
    else if(op==='cfg')err=configure(room,tok,req.ch||{});
    else if(op==='start')err=start(room,tok,now,rndSecure);
    else if(op==='say')err=say(room,tok,req.k,now);
    else if(op==='leave'){if(room.solo)soloLeave(store,room,now);
      else{const s=room.seats[seat];if(room.q&&room.st==='lobby'&&s&&s.ac&&s.paid){stakeBack(store,s.ac,s.paid,now);s.paid=0;}err=leave(room,tok,now);}}
    advance(room,now,rndSecure);rateQuick(store,room,now);settleSolo(store,room,now);settleNet(store,room,now);if(room.q&&room.st!=='lobby')openDrop(room.q.key,room.code);
    room.exp=now+ROOM_TTL;
    if(room.v!==v0||op==='join'){if(!(await store.save(room,rec.ver)))continue;}
    track(store,room,now);
    const since=req.since==null?-1:+req.since;
    const out=Object.assign({},viewFor(room,seat,since,+req.cs||0),{now});
    if(op==='join')Object.assign(out,{tok,seat});
    if(err)out.err=err;
    out.due=nextDue(room);out._l0=l0;out._c0=c0;
    return out;}
  return {err:'busy'};}

// a seat at an open table: the first one of this kind that still waits, or a new one
async function quickJoin(store,req,ac,now){
  if(!ac)return {err:'bad acct'};const t=tierOf(req.tier);if(!t)return {err:'bad tier'};
  const me=accGet(store,ac,now);if(me.r<t.need)return {err:'rank',need:t.need};
  if(ecoOf(me).coins<t.stake)return {err:'coins',need:t.stake};
  const o=quickOpts(t,req.mode,req.n),key=quickKey(t.id,o.mode,o.n);me.nm=cleanName(req.name);accPut(store,ac,me);
  const list=(OPEN.get(key)||[]).slice();
  for(const code of list){const r=await sitAt(store,code,req,ac,now,true);if(r)return r;}
  return newTable(store,o,t,req,ac,now,key,false);}
// a seat at one waiting table, the stake paid; null if this table will not do (the quick game then tries the next one)
async function sitAt(store,code,req,ac,now,quick){
  for(let attempt=0;attempt<4;attempt++){const rec=await store.load(code);const room=rec&&rec.room;
    const key=room&&room.q?room.q.key:null,drop=()=>{if(key)openDrop(key,code);};
    if(!room||room.st!=='lobby'||!room.q||(room.qAt&&room.qAt<now+1500)||!room.seats.some(s=>s.k==='o')){drop();return quick?null:{err:'gone'};}
    const t=tierOf(room.q.tier),me=accGet(store,ac,now);
    if(me.r<t.need)return quick?null:{err:'rank',need:t.need};if(ecoOf(me).coins<t.stake)return quick?null:{err:'coins',need:t.stake};
    // the same person twice at one table is not a game
    if(room.seats.some(s=>s.k==='h'&&s.ac===ac))return quick?null:{err:'seated'};
    const r=join(room,req.name,now,rndSecure,'',ac);if(r.err){drop();return quick?null:{err:'gone'};}
    room.exp=now+ROOM_TTL;room.seats[r.seat].paid=t.stake;
    if(!(await store.save(room,rec.ver)))continue;
    if(!stakeTake(store,ac,t.stake,now)){/* spent meanwhile: give the seat back */const rec2=await store.load(code);if(rec2){leave(rec2.room,r.tok,now);await store.save(rec2.room,rec2.ver);track(store,rec2.room,now);}return {err:'coins',need:t.stake};}
    if(!room.seats.some(s=>s.k==='o'))drop();
    track(store,room,now);
    return Object.assign({tok:r.tok,seat:r.seat},viewFor(room,r.seat,-1,0),{now,due:nextDue(room),_l0:0,_c0:0,_changed:true});}
  return quick?null:{err:'busy'};}
async function newTable(store,o,t,req,ac,now,key,list){
  for(let k=0;k<8;k++){const r=newRoom(o,req.name,now,rndSecure,ac,Object.assign({tier:t.id,stake:t.stake,key},list?{list:1}:{}));r.room.seats[0].paid=t.stake;
    if(list)r.room.qAt=0; // waits for people until the host starts it (or it fills up)
    if(await store.create(r.room)){if(!stakeTake(store,ac,t.stake,now)){r.room.st='closed';await store.save(r.room,1);return {err:'coins',need:t.stake};}
      if(key)openAdd(key,r.room.code);track(store,r.room,now);return Object.assign({tok:r.tok,seat:0},viewFor(r.room,0,-1,0),{now,due:nextDue(r.room)});}}
  return {err:'busy'};}
// a player sets up a table of their own in the list
async function tableCreate(store,req,ac,now){
  if(!ac)return {err:'bad acct'};const t=tierOf(req.tier);if(!t)return {err:'bad tier'};
  const me=accGet(store,ac,now);if(me.r<t.need)return {err:'rank',need:t.need};
  if(ecoOf(me).coins<t.stake)return {err:'coins',need:t.stake};
  const o=tableOpts(t,req);me.nm=cleanName(req.name);accPut(store,ac,me);
  // a plain table can also be found by the quick game
  const plain=o.deck===36&&!Object.keys(o.rules).length,key=plain?quickKey(t.id,o.mode,o.n):null;
  return newTable(store,o,t,req,ac,now,key,true);}
async function tableJoin(store,req,ac,now){if(!ac)return {err:'bad acct'};const code=normCode(req.code);if(!code)return {err:'bad code'};
  const me=accGet(store,ac,now);me.nm=cleanName(req.name);accPut(store,ac,me);
  return sitAt(store,code,req,ac,now,false);}

// an in-memory store for local testing
function memStore(){const m=new Map();
  return {
    async load(code){const s=m.get(code);return s?{room:JSON.parse(s.d),ver:s.ver}:null;},
    async save(room,ver){const s=m.get(room.code);if(!s||s.ver!==ver)return false;m.set(room.code,{d:JSON.stringify(room),ver:ver+1});return true;},
    async create(room){if(m.has(room.code))return false;m.set(room.code,{d:JSON.stringify(room),ver:1});return true;},
    acc:new Map(),_m:m};}


;
// Friends' table server for one small machine: plain Node, no packages.
// HTTPS and the certificate are handled by Caddy in front; this listens on 127.0.0.1:8080.
//  POST /api  — one request, one answer (create, join, moves...; also the fallback when WebSocket is unavailable)
//  GET  /ws   — WebSocket: the same requests, plus everything that happens at the table is pushed at once
// Rooms live in memory and are saved to disk every few seconds, so a restart loses nothing.
const http=require('http'),fs=require('fs'),crypto=require('crypto'),path=require('path');
const core=typeof handle==='function'?{handle,memStore,viewFor,vkNotify,okNotify}:require('./dist/core.js');
const PORT=+process.env.PORT||8080,DATA=process.env.DATA||'/var/lib/durak/rooms.json',STATIC=process.env.STATIC||'';

/* ---------- rooms: in memory, saved to disk ---------- */
const store=core.memStore();let dirty=false,accDirty=false;
const ACC=path.join(path.dirname(DATA),'accounts.json');
var hadAccounts=fs.existsSync(ACC); // a new machine (no accounts yet) takes the last backup back, see below
store.iapUsed=new Map();
try{const raw=JSON.parse(fs.readFileSync(ACC,'utf8'));
  if(Array.isArray(raw))store.acc=new Map(raw);else{store.acc=new Map(raw.a||[]);store.iapUsed=new Map(raw.u||[]);}
  console.log('loaded accounts',store.acc.size,'purchases',store.iapUsed.size);}catch(e){store.acc=new Map();}
/* secrets (platform keys) are not in the code: they are typed into the machine's metadata, key "durak-secrets", as JSON */
store.secrets={};
function loadSecrets(){require('http').get({host:'169.254.169.254',path:'/computeMetadata/v1/instance/attributes/durak-secrets',headers:{'Metadata-Flavor':'Google'},timeout:3000},res=>{
  let b='';res.setEncoding('utf8');res.on('data',d=>b+=d);res.on('end',()=>{if(res.statusCode!==200)return;try{store.secrets=JSON.parse(b);console.log('secrets loaded:',Object.keys(store.secrets).join(','));}catch(e){console.error('secrets: not JSON');}});})
  .on('error',()=>{}).on('timeout',function(){this.destroy();});}
if(process.env.SECRETS){try{store.secrets=JSON.parse(process.env.SECRETS);}catch(e){}}else{loadSecrets();setInterval(loadSecrets,10*60*1000);}
store.accDirty=()=>{accDirty=true;};
try{const raw=JSON.parse(fs.readFileSync(DATA,'utf8'));const now=Date.now();
  for(const [code,rec] of raw){const r=JSON.parse(rec.d);if(r.exp>now){r.cx={};rec.d=JSON.stringify(r);store._m.set(code,rec);}}
  console.log('loaded rooms',store._m.size);}catch(e){console.log('no saved rooms');}
const save0=store.save,create0=store.create;
store.save=async(r,v)=>{const ok=await save0(r,v);if(ok)dirty=true;return ok;};
store.create=async r=>{const ok=await create0(r);if(ok)dirty=true;return ok;};
function persistAcc(){if(!accDirty)return;accDirty=false;
  try{fs.mkdirSync(path.dirname(ACC),{recursive:true});fs.writeFileSync(ACC+'.tmp',JSON.stringify({a:[...store.acc],u:[...store.iapUsed]}));fs.renameSync(ACC+'.tmp',ACC);}catch(e){console.error('acc save failed',e.message);}}
setInterval(persistAcc,5000);
function persist(){if(!dirty)return;dirty=false;const now=Date.now();
  for(const [code,rec] of store._m){try{if(JSON.parse(rec.d).exp<now){store._m.delete(code);conns.delete(code);}}catch(e){store._m.delete(code);}}
  try{fs.mkdirSync(path.dirname(DATA),{recursive:true});fs.writeFileSync(DATA+'.tmp',JSON.stringify([...store._m]));fs.renameSync(DATA+'.tmp',DATA);}catch(e){console.error('save failed',e.message);}}
setInterval(persist,5000);
process.on('SIGTERM',()=>{dirty=true;persist();persistAcc();process.exit(0);});
process.on('SIGINT',()=>{dirty=true;persist();persistAcc();process.exit(0);});

/* ---------- backups: accounts (coins, purchases, ranks) are copied to Object Storage every few hours ---------- */
// The bucket is named in the metadata secrets as "backup"; the machine's own service account (storage.uploader +
// storage.viewer) gives the key, so no secret is kept here. Files rotate by weekday and hour (28 of them, overwritten),
// plus one per month and "latest". A machine that starts without accounts.json takes "latest" back by itself.
const zlib=require('zlib');
function iamToken(cb){require('http').get({host:'169.254.169.254',path:'/computeMetadata/v1/instance/service-accounts/default/token',headers:{'Metadata-Flavor':'Google'},timeout:3000},res=>{
  let b='';res.setEncoding('utf8');res.on('data',d=>b+=d);res.on('end',()=>{try{cb(res.statusCode===200?JSON.parse(b).access_token:null);}catch(e){cb(null);}});})
  .on('error',()=>cb(null)).on('timeout',function(){this.destroy();});}
function s3(method,key,body,cb){const bucket=store.secrets.backup;if(!bucket)return cb&&cb(0,'no bucket');
  iamToken(tok=>{if(!tok)return cb&&cb(0,'no token');
    const rq=require('https').request({host:'storage.yandexcloud.net',path:'/'+encodeURIComponent(bucket)+'/'+key,method,headers:Object.assign({Authorization:'Bearer '+tok},body?{'Content-Length':body.length,'Content-Type':'application/gzip'}:{}),timeout:30000},res=>{
      const parts=[];res.on('data',d=>parts.push(d));res.on('end',()=>cb&&cb(res.statusCode,Buffer.concat(parts)));});
    rq.on('error',e=>cb&&cb(0,e.message));rq.on('timeout',()=>rq.destroy());if(body)rq.write(body);rq.end();});}
let lastBackup={at:0,ok:false,err:''};
function backup(){if(!store.secrets.backup)return;
  if(!hadAccounts&&!restoreDone){setTimeout(backup,30000);return;} // never write over the copy before it was taken back
  const body=zlib.gzipSync(JSON.stringify({a:[...store.acc],u:[...store.iapUsed],at:Date.now()}));
  const d=new Date(Date.now()+3*3600e3),slot='d'+d.getUTCDay()+'-h'+String(Math.floor(d.getUTCHours()/6)*6).padStart(2,'0'),month='m'+d.toISOString().slice(0,7);
  let left=3,bad='';const done=(code,err)=>{if(code!==200)bad=bad||String(code||err);if(--left)return;
    lastBackup={at:Date.now(),ok:!bad,err:bad};console.log(bad?'backup failed: '+bad:'backup ok '+store.acc.size+' accounts');};
  s3('PUT','backups/latest.json.gz',body,done);s3('PUT','backups/'+slot+'.json.gz',body,done);s3('PUT','backups/'+month+'.json.gz',body,done);}
setInterval(backup,6*3600e3);
// first backup soon after the start (secrets come from the metadata a moment later)
setTimeout(backup,90*1000);
// a machine without accounts takes the last copy back
var hadAccounts,restoreDone=false;let restoreBusy=false;
function maybeRestore(){if(hadAccounts||restoreDone||restoreBusy||!store.secrets.backup)return;restoreBusy=true;
  s3('GET','backups/latest.json.gz',null,(code,buf)=>{restoreBusy=false;
    if(code===404){restoreDone=true;console.log('restore: no copy yet');return;}
    if(code!==200){console.log('restore: will try again ('+code+')');return;}restoreDone=true;
    try{const raw=JSON.parse(zlib.gunzipSync(buf).toString('utf8'));let n=0;
      for(const [a,x] of raw.a||[])if(!store.acc.has(a)){store.acc.set(a,x);n++;}
      for(const [k,v] of raw.u||[])if(!store.iapUsed.has(k))store.iapUsed.set(k,v);
      accDirty=true;persistAcc();console.log('restored',n,'accounts from the backup');}catch(e){console.error('restore failed',e.message);}});}
setInterval(maybeRestore,5000);

/* ---------- updating itself: a newer server on GitHub is picked up when no game is being played ---------- */
// the service downloads server.js on every start, so leaving is enough; rooms and accounts are saved first
const SELF=process.env.SELF_URL||'https://raw.githubusercontent.com/ttgms/durak/main/server/server.js';
let newerSince=0;
function busyTables(){let n=0;for(const [,rec] of store._m){try{if(JSON.parse(rec.d).st==='play')n++;}catch(e){}}return n;}
function checkSelf(){if(process.env.NO_SELF_UPDATE)return;
  require('https').get(SELF,res=>{if(res.statusCode!==200){res.resume();return;}let b='';res.setEncoding('utf8');res.on('data',d=>b+=d);
    res.on('end',()=>{let mine='';try{mine=fs.readFileSync(__filename,'utf8');}catch(e){return;}
      if(!b||b.length<1000||b===mine){newerSince=0;return;}
      if(!newerSince)newerSince=Date.now();
      // wait for a quiet moment, but not for ever
      if(busyTables()===0||Date.now()-newerSince>3*3600e3){console.log('newer server found, restarting');dirty=true;persist();accDirty=true;persistAcc();process.exit(0);}});})
  .on('error',()=>{});}
setInterval(checkSelf,5*60*1000);

/* ---------- who is connected to which table ---------- */
const conns=new Map(); // code -> Set of sockets (sock.seat)
function attach(sock,code,seat){if(sock.code&&sock.code!==code){const s=conns.get(sock.code);if(s)s.delete(sock);}
  sock.code=code;sock.seat=seat;if(!conns.has(code))conns.set(code,new Set());conns.get(code).add(sock);}
function detach(sock){const s=sock.code&&conns.get(sock.code);if(s)s.delete(sock);}
const verOf=code=>{const r=store._m.get(code);return r?r.ver:0;};
function roomOf(code){const r=store._m.get(code);return r?JSON.parse(r.d):null;}
// everyone at the table (but the one who asked) gets what changed since l0 / c0
function broadcast(code,l0,c0,skip){const set=conns.get(code);if(!set||!set.size)return;const room=roomOf(code);if(!room)return;const now=Date.now();
  for(const sock of set){if(sock===skip||sock.seat==null||sock.seat<0)continue;
    try{wsSend(sock,Object.assign(core.viewFor(room,sock.seat,l0,c0),{now,push:1,from:l0}));}catch(e){}}}
// the server's own moves (bots, timers) when they fall due
const timers=new Map();
function wakeAt(code,due){clearTimeout(timers.get(code));if(!due)return;
  timers.set(code,setTimeout(()=>tick(code),Math.max(20,due-Date.now()+20)));}
async function tick(code){timers.delete(code);const v0=verOf(code);
  const r=await core.handle(store,{op:'tick',code});if(!r||r.err)return;
  if(verOf(code)!==v0)broadcast(code,r._l0,r._c0,null);wakeAt(code,r.due);}
const strip=o=>{const r={};for(const k in o)if(k[0]!=='_')r[k]=o[k];return r;};
async function serve(req,sock){
  if(!req||typeof req!=='object')return {err:'bad request'};if(req.op==='tick'||req.op==='sweep')return {err:'bad op'};
  if(req.op==='ping')return {pong:1,now:Date.now()};
  const code0=req.code?String(req.code):'';
  const res=await core.handle(store,req);
  const code=res.room&&res.room.code;
  if(code){
    if(sock&&res.room.me!=null&&res.room.me>=0)attach(sock,code,res.room.me);
    // anything that changed the table is pushed to the others
    if(res._l0!==undefined&&res._changed)broadcast(code,res._l0,res._c0,sock);
    wakeAt(code,res.due);}
  if(req.rid!=null)res.rid=req.rid;
  return strip(res);}
// note whether a request changed the room (compare stored versions around the call)
const handle0=core.handle;core.handle=async(st,req)=>{const c=req.code?String(req.code):'';
  const norm=c&&typeof normCode==='function'?normCode(c):c;const v0=norm?verOf(norm):0;const r=await handle0(st,req);
  if(r&&r.room&&r.room.code)r._changed=req.op==='create'||req.op==='join'||verOf(r.room.code)!==v0;return r;};

// tables everybody walked away from close and give the stakes back
setInterval(()=>{core.handle(store,{op:'sweep',_internal:1}).catch(e=>console.error('sweep',e));},30000);

/* ---------- HTTP ---------- */
const CORS={'Access-Control-Allow-Origin':'*','Access-Control-Allow-Headers':'Content-Type','Access-Control-Allow-Methods':'POST, GET, OPTIONS'};
const server=http.createServer((rq,rs)=>{
  if(rq.method==='OPTIONS'){rs.writeHead(204,CORS);rs.end();return;}
  // payment notifications: VK posts a form, OK asks with GET
  if(rq.url.split('?')[0]==='/vkpay'){
    if(rq.method==='POST'){let b='';rq.on('data',d=>{b+=d;if(b.length>65536)rq.destroy();});
      rq.on('end',()=>{let out;try{out=core.vkNotify(store,Object.fromEntries(new URLSearchParams(b)),Date.now());}catch(e){console.error(e);out={error:{error_code:1,error_msg:'server error',critical:false}};}
        rs.writeHead(200,{'Content-Type':'application/json; charset=utf-8'});rs.end(JSON.stringify(out));});return;}
    const q=Object.fromEntries(new URL(rq.url,'http://x').searchParams);delete q.ok;let out;
    try{out=core.okNotify(store,q,Date.now());}catch(e){console.error(e);out={err:true,code:9999,body:'<error/>'};}
    const hd={'Content-Type':'application/xml; charset=utf-8'};if(out.err)hd['invocation-error']=String(out.code);rs.writeHead(200,hd);rs.end(out.body);return;}
  if(rq.url==='/health'){rs.writeHead(200,Object.assign({'Content-Type':'text/plain'},CORS));rs.end('ok '+store._m.size+(store.secrets.backup?' backup '+(lastBackup.at?(lastBackup.ok?'ok ':'FAILED '+lastBackup.err+' ')+Math.round((Date.now()-lastBackup.at)/60000)+'m ago':'pending'):''));return;}
  if(rq.method==='POST'&&rq.url.split('?')[0]==='/api'){let b='';let big=false;
    rq.on('data',d=>{b+=d;if(b.length>65536){big=true;rq.destroy();}});
    rq.on('end',async()=>{if(big)return;let out;try{out=await serve(JSON.parse(b||'{}'),null);}catch(e){console.error(e);out={err:'server'};}
      rs.writeHead(200,Object.assign({'Content-Type':'application/json','Cache-Control':'no-store'},CORS));rs.end(JSON.stringify(out));});return;}
  if(STATIC&&rq.method==='GET'){let f=rq.url.split('?')[0];if(f==='/')f='/index.html';const fp=path.join(STATIC,f);
    if(fp.startsWith(STATIC)&&fs.existsSync(fp)&&fs.statSync(fp).isFile()){
      let data=fs.readFileSync(fp);if(f==='/index.html'&&process.env.INJECT)data=Buffer.from(data.toString().replace('<head>','<head>'+process.env.INJECT));
      rs.writeHead(200,{'Content-Type':f.endsWith('.html')?'text/html; charset=utf-8':f.endsWith('.mp3')?'audio/mpeg':'application/octet-stream'});rs.end(data);return;}}
  rs.writeHead(404,CORS);rs.end();});

/* ---------- WebSocket (RFC 6455, text frames only) ---------- */
server.on('upgrade',(rq,socket)=>{
  if(rq.url.split('?')[0]!=='/ws'||(rq.headers.upgrade||'').toLowerCase()!=='websocket'){socket.destroy();return;}
  const key=rq.headers['sec-websocket-key'];if(!key){socket.destroy();return;}
  const acc=crypto.createHash('sha1').update(key+'258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64');
  socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: '+acc+'\r\n\r\n');
  socket.setNoDelay(true);socket.alive=true;let buf=Buffer.alloc(0),parts=[];
  socket.on('data',d=>{buf=Buffer.concat([buf,d]);
    while(buf.length>=2){const fin=buf[0]&0x80,op=buf[0]&0x0f,masked=buf[1]&0x80;let len=buf[1]&0x7f,off=2;
      if(len===126){if(buf.length<4)return;len=buf.readUInt16BE(2);off=4;}
      else if(len===127){if(buf.length<10)return;len=Number(buf.readBigUInt64BE(2));off=10;}
      if(len>65536){socket.destroy();return;}
      const mk=masked?4:0;if(buf.length<off+mk+len)return;
      let payload=buf.subarray(off+mk,off+mk+len);if(masked){const m=buf.subarray(off,off+4);payload=Buffer.from(payload);for(let i=0;i<payload.length;i++)payload[i]^=m[i&3];}
      buf=buf.subarray(off+mk+len);
      if(op===8){try{socket.end(Buffer.from([0x88,0]));}catch(e){}return;}
      if(op===9){wsFrame(socket,0xA,payload);continue;}
      if(op===10){socket.alive=true;continue;}
      if(op===1||op===0){parts.push(payload);if(!fin)continue;const text=Buffer.concat(parts).toString('utf8');parts=[];
        socket.alive=true;let req;try{req=JSON.parse(text);}catch(e){continue;}
        serve(req,socket).then(out=>wsSend(socket,out),e=>{console.error(e);wsSend(socket,{err:'server',rid:req&&req.rid});});}}});
  socket.on('close',()=>detach(socket));socket.on('error',()=>detach(socket));});
function wsFrame(sock,op,payload){const n=payload.length;let head;
  if(n<126)head=Buffer.from([0x80|op,n]);else if(n<65536){head=Buffer.alloc(4);head[0]=0x80|op;head[1]=126;head.writeUInt16BE(n,2);}
  else{head=Buffer.alloc(10);head[0]=0x80|op;head[1]=127;head.writeBigUInt64BE(BigInt(n),2);}
  if(!sock.destroyed)sock.write(Buffer.concat([head,payload]));}
function wsSend(sock,obj){wsFrame(sock,1,Buffer.from(JSON.stringify(obj)));}
// ping every 25 s; drop connections that stopped answering
setInterval(()=>{for(const set of conns.values())for(const s of set){if(!s.alive){s.destroy();set.delete(s);continue;}s.alive=false;wsFrame(s,9,Buffer.alloc(0));}},25000);

server.listen(PORT,process.env.HOST||'127.0.0.1',()=>console.log('durak server on',PORT));
