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
  const m=/^([А-ЯЁ]+)-?(\d{3})$/.exec(s);return m?m[1]+'-'+m[2]:'';}
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

function seatOf(room,tok){return tok?room.seats.findIndex(s=>s.k==='h'&&s.tok===tok):-1;}
function humans(room){return room.seats.filter(s=>s.k==='h').length;}

function join(room,name,now,rnd,tok,ac){
  const was=seatOf(room,tok);if(was>=0){room.seats[was].seen=now;room.seats[was].away=false;return {seat:was,tok};}
  if(room.st!=='lobby'){ // a game is on: a newcomer may take over a seat a bot is keeping for someone who left
    return {err:'started'};}
  const i=room.seats.findIndex(s=>s.k==='o');if(i<0)return {err:'full'};
  const t=rndToken(rnd);room.seats[i]=Object.assign({k:'h',nm:cleanName(name),tok:t,seen:now},ac?{ac}:{});room.v++;
  // a full open table does not wait any longer
  if(room.q&&!room.seats.some(s=>s.k==='o'))room.qAt=Math.min(room.qAt,now+1500);
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
  if(room.q&&tok!==null)return 'quick'; // open tables start by themselves
  if(!room.q&&seatOf(room,tok)!==room.host)return 'not host';if(room.st==='play')return 'already';
  const used=new Set();
  room.seats.forEach((s,i)=>{if(s.k==='h'){s.away=false;s.idle=false;s.to=0;return;}
    if(room.q)s.ch=null;
    let ch=s.ch&&!used.has(s.ch)?s.ch:null;
    if(!ch){const pool=BOT_CHARS.filter(c=>!used.has(c));ch=pool[Math.floor(rnd()*pool.length)];}
    used.add(ch);room.seats[i]={k:'b',ch};});
  room.st='play';room.seed=1+Math.floor(rnd()*2147483646);room.game++;room.log=[];room.fin=null;room.at=now;room.dl=0;
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
  for(const q of this.throwers()){if(this.passed.has(q))continue;if(this.hands[q].some(c=>this.canAttack(q,c)))return;this.passed.add(q);this._ap.push(q);}
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
  const g=new Game(gameOpts(room));g.settle=settleRec;g.events=[];const meta=[];
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
  room.dl=room.at+room.opts.timer*1000;}
function botDelay(room,g,tm){
  if(room.seats[tm].away||room.seats[tm].idle)return 700;
  const run=lastRun(room,g);
  // give a human attacker time to add a second card before a bot answers
  const more=run>=0&&!controlled(room,run)&&g.hands[run].some(c=>g.canAttack(run,c));
  return 1000+(more?1300:0)+(g.deck.length===0?300:0);}
function safeMove(g,p){
  if(p===g.def&&!g.taking&&g.undefended().length)return {t:'take'};
  if(!g.table.length){const c=g.hands[p].slice().sort((a,b)=>(g.isTrump(a)-g.isTrump(b))||g.rk(a)-g.rk(b)).find(c=>g.canAttack(p,c));return {t:'attack',c:c.id};}
  return {t:'done'};}
function botMove(room,g,p){
  // bots look at the table: a wrong card is sometimes called out
  if(g.rules.cheat&&g.cheater()>=0&&g.cheater()!==p&&room.seats[p].k==='b'&&Math.random()<.45)return {t:'acc'};
  const st=room.seats[p].k==='b'?STYLES[BOT_STYLE[room.opts.level]]:STYLES.bold;
  const m=aiMove(g,p,st)||g.legal(p).find(x=>x.t==='take'||x.t==='done');
  return {t:m.t,c:m.c?m.c.id:undefined,i:m.i};}
// let bots and timers do what is due; called on every request. Returns true if anything moved.
function advance(room,now,rnd){
  // an open table starts when it is full or has waited long enough; one that everybody left closes
  if(room.q&&room.st==='lobby'){
    if(!room.seats.some(s=>s.k==='h')){room.st='closed';room.v++;return true;}
    if(now>=room.qAt){start(room,null,now,rnd||Math.random);return true;}
    return false;}
  if(room.st!=='play')return false;let moved=false;
  // players silent for a long time are looked after by a bot until they come back
  for(const s of room.seats)if(s.k==='h'&&!s.away&&now-(s.seen||0)>45000){s.away=true;room.v++;moved=true;}
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
  return {code:room.code,v:room.v,st:room.st,game:room.game,host:room.host,me:s,opts:room.opts,dl:room.dl,q:room.q||undefined,qAt:room.q?room.qAt:undefined,
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
  {id:'merch',nm:'Купеческий', stake:1000,  need:300,  level:'medium', mult:1.5},
  {id:'boyar',nm:'Боярский',   stake:10000, need:1000, level:'hard',   mult:2},
  {id:'tsar', nm:'Царский',    stake:50000, need:2500, level:'hard',   mult:3}];
const TITLES=[[0,'Новичок'],[300,'Купец'],[1000,'Боярин'],[2500,'Царь']];
const PLACE_PTS={2:[20],3:[20,8],4:[20,10,5]},FOOL_PTS=-12,DRAW_PTS=3;
const SHARE={2:[1],3:[.6,.4],4:[.5,.3,.2]};

function tierOf(id){return TIERS.find(t=>t.id===id)||null;}
function rankOf(r){let x=TITLES[0];for(const k of TITLES)if(r>=k[0])x=k;return x[1];}
function nextRank(r){for(const k of TITLES)if(r<k[0])return {at:k[0],nm:k[1]};return null;}
function weekOf(now){return Math.floor((now+3*3600e3-4*86400e3)/604800e3);} // weeks start on Monday, Moscow time
function quickKey(tier,mode,n){return tier+'|'+mode+'|'+n;}
function quickOpts(t,mode,n){return {deck:36,n:Math.max(2,Math.min(4,+n||2)),mode:mode==='perevodnoy'?'perevodnoy':'podkidnoy',rules:{},timer:30,level:t.level};}

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
function profile(x){const nx=nextRank(x.r);return {r:x.r,rank:rankOf(x.r),next:nx,g:x.g,w:x.w,wp:x.wp};}
// applied once per finished quick game
function rateQuick(store,room,now){
  if(!room.q||!room.fin||room.fin.rated)return false;
  const res=quickResult(room,room.fin);room.fin.pay=res.pay;room.fin.pts=res.pts;room.fin.place=res.place;room.fin.rated=1;
  room.seats.forEach((s,i)=>{if(s.k!=='h'||!s.ac)return;const x=accGet(store,s.ac,now);
    x.r=Math.max(0,x.r+res.pts[i]);x.g++;if(res.place[i]>=0&&i!==room.fin.fool)x.w++;x.wp+=Math.max(0,res.pts[i]);x.nm=s.nm;x.t=now;accPut(store,s.ac,x);});
  room.v++;return true;}
function topLists(store,now,me){
  const wk=weekOf(now),all=[...store.acc.entries()].filter(([,x])=>x.g>0);
  const week=all.filter(([,x])=>x.wk===wk&&x.wp>0).sort((a,b)=>b[1].wp-a[1].wp);
  const ever=all.slice().sort((a,b)=>b[1].r-a[1].r);
  const row=([a,x])=>({nm:x.nm,r:x.r,wp:x.wp,rank:rankOf(x.r),me:a===me||undefined});
  return {week:week.slice(0,20).map(row),ever:ever.slice(0,20).map(row),
    myWeek:me?week.findIndex(([a])=>a===me)+1:0,myEver:me?ever.findIndex(([a])=>a===me)+1:0};}


;
// Request handling for the friends' table, independent of where rooms are stored and how messages travel.
// store: {load(code) -> {room,ver}|null, save(room,ver) -> bool (false if someone changed it meanwhile), create(room) -> bool}
// Every change is: load, change, save-if-unchanged; on a clash the whole step is simply repeated.

function rndSecure(){try{const b=require('crypto').randomBytes(4);return b.readUInt32LE(0)/4294967296;}catch(e){return Math.random();}}
const OPS=new Set(['create','join','poll','act','cfg','start','say','leave','tick','quick','me','top']);
// open tables that still wait for people, by kind (tier|mode|players); only a hint, every table is checked on load
const OPEN=new Map();
function openAdd(key,code){if(!OPEN.has(key))OPEN.set(key,[]);OPEN.get(key).push(code);}
function openDrop(key,code){const a=OPEN.get(key);if(!a)return;const i=a.indexOf(code);if(i>=0)a.splice(i,1);}

async function handle(store,req,now){
  now=now||Date.now();const op=String(req.op||'');
  if(!OPS.has(op))return {err:'bad op'};
  if(!store.acc)store.acc=new Map();
  const ac=cleanAcct(req.acct);
  if(op==='me'){if(!ac)return {err:'bad acct'};const x=accGet(store,ac,now);return {me:profile(x),tiers:TIERS,now};}
  if(op==='top')return Object.assign(topLists(store,now,ac),{now});
  if(op==='quick')return quickJoin(store,req,ac,now);
  if(op==='create'){
    for(let k=0;k<8;k++){const r=newRoom(req.opts,req.name,now,rndSecure);
      if(await store.create(r.room))return Object.assign({tok:r.tok,seat:0},viewFor(r.room,0,-1,0),{now});}
    return {err:'busy'};}
  const code=normCode(req.code);if(!code)return {err:'bad code'};
  for(let attempt=0;attempt<6;attempt++){
    const rec=await store.load(code);if(!rec||rec.room.st==='closed'||rec.room.exp<now)return {err:'no room'};
    const room=rec.room,v0=room.v,l0=room.log.length,c0=room.ci;let err=null,seat=seatOf(room,req.tok),tok=req.tok;
    if(op==='tick'){advance(room,now,rndSecure);rateQuick(store,room,now);if(room.q&&room.st!=='lobby')openDrop(room.q.key,room.code);
      if(room.v!==v0&&!(await store.save(room,rec.ver)))continue;return {room:{code:room.code},due:nextDue(room),_l0:l0,_c0:c0,now};}
    if(op==='join'){const r=join(room,req.name,now,rndSecure,req.tok,ac);if(r.err)return {err:r.err};seat=r.seat;tok=r.tok;}
    else{if(seat<0)return {err:'not seated'};const s=room.seats[seat];
      if(now-(s.seen||0)>15000||(s.away&&!s.left)){s.seen=now;s.away=false;room.v++;}}
    if(op==='act')err=act(room,tok,req.m||{},now);
    else if(op==='cfg')err=configure(room,tok,req.ch||{});
    else if(op==='start')err=start(room,tok,now,rndSecure);
    else if(op==='say')err=say(room,tok,req.k,now);
    else if(op==='leave')err=leave(room,tok,now);
    advance(room,now,rndSecure);rateQuick(store,room,now);if(room.q&&room.st!=='lobby')openDrop(room.q.key,room.code);
    room.exp=now+ROOM_TTL;
    if(room.v!==v0||op==='join'){if(!(await store.save(room,rec.ver)))continue;}
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
  const o=quickOpts(t,req.mode,req.n),key=quickKey(t.id,o.mode,o.n);me.nm=cleanName(req.name);accPut(store,ac,me);
  const list=(OPEN.get(key)||[]).slice();
  for(const code of list){
    for(let attempt=0;attempt<4;attempt++){const rec=await store.load(code);
      if(!rec||rec.room.st!=='lobby'||!rec.room.q||rec.room.qAt<now+1500||!rec.room.seats.some(s=>s.k==='o')){openDrop(key,code);break;}
      const room=rec.room;
      // the same person twice at one table is not a game
      if(room.seats.some(s=>s.k==='h'&&s.ac===ac)){openDrop(key,code);break;}
      const r=join(room,req.name,now,rndSecure,'',ac);if(r.err){openDrop(key,code);break;}
      room.exp=now+ROOM_TTL;
      if(!(await store.save(room,rec.ver)))continue;
      if(!room.seats.some(s=>s.k==='o'))openDrop(key,code);
      return Object.assign({tok:r.tok,seat:r.seat},viewFor(room,r.seat,-1,0),{now,due:nextDue(room),_l0:0,_c0:0,_changed:true});}}
  for(let k=0;k<8;k++){const r=newRoom(o,req.name,now,rndSecure,ac,{tier:t.id,stake:t.stake,key});
    if(await store.create(r.room)){openAdd(key,r.room.code);return Object.assign({tok:r.tok,seat:0},viewFor(r.room,0,-1,0),{now,due:nextDue(r.room)});}}
  return {err:'busy'};}

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
const core=typeof handle==='function'?{handle,memStore,viewFor}:require('./dist/core.js');
const PORT=+process.env.PORT||8080,DATA=process.env.DATA||'/var/lib/durak/rooms.json',STATIC=process.env.STATIC||'';

/* ---------- rooms: in memory, saved to disk ---------- */
const store=core.memStore();let dirty=false,accDirty=false;
const ACC=path.join(path.dirname(DATA),'accounts.json');
try{store.acc=new Map(JSON.parse(fs.readFileSync(ACC,'utf8')));console.log('loaded accounts',store.acc.size);}catch(e){store.acc=new Map();}
store.accDirty=()=>{accDirty=true;};
try{const raw=JSON.parse(fs.readFileSync(DATA,'utf8'));const now=Date.now();
  for(const [code,rec] of raw){const r=JSON.parse(rec.d);if(r.exp>now){r.cx={};rec.d=JSON.stringify(r);store._m.set(code,rec);}}
  console.log('loaded rooms',store._m.size);}catch(e){console.log('no saved rooms');}
const save0=store.save,create0=store.create;
store.save=async(r,v)=>{const ok=await save0(r,v);if(ok)dirty=true;return ok;};
store.create=async r=>{const ok=await create0(r);if(ok)dirty=true;return ok;};
function persistAcc(){if(!accDirty)return;accDirty=false;
  try{fs.mkdirSync(path.dirname(ACC),{recursive:true});fs.writeFileSync(ACC+'.tmp',JSON.stringify([...store.acc]));fs.renameSync(ACC+'.tmp',ACC);}catch(e){console.error('acc save failed',e.message);}}
setInterval(persistAcc,5000);
function persist(){if(!dirty)return;dirty=false;const now=Date.now();
  for(const [code,rec] of store._m){try{if(JSON.parse(rec.d).exp<now){store._m.delete(code);conns.delete(code);}}catch(e){store._m.delete(code);}}
  try{fs.mkdirSync(path.dirname(DATA),{recursive:true});fs.writeFileSync(DATA+'.tmp',JSON.stringify([...store._m]));fs.renameSync(DATA+'.tmp',DATA);}catch(e){console.error('save failed',e.message);}}
setInterval(persist,5000);
process.on('SIGTERM',()=>{dirty=true;persist();persistAcc();process.exit(0);});
process.on('SIGINT',()=>{dirty=true;persist();persistAcc();process.exit(0);});

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
function schedule(code,due){clearTimeout(timers.get(code));if(!due)return;
  timers.set(code,setTimeout(()=>tick(code),Math.max(20,due-Date.now()+20)));}
async function tick(code){timers.delete(code);const v0=verOf(code);
  const r=await core.handle(store,{op:'tick',code});if(!r||r.err)return;
  if(verOf(code)!==v0)broadcast(code,r._l0,r._c0,null);schedule(code,r.due);}
const strip=o=>{const r={};for(const k in o)if(k[0]!=='_')r[k]=o[k];return r;};
async function serve(req,sock){
  if(!req||typeof req!=='object')return {err:'bad request'};if(req.op==='tick')return {err:'bad op'};
  if(req.op==='ping')return {pong:1,now:Date.now()};
  const code0=req.code?String(req.code):'';
  const res=await core.handle(store,req);
  const code=res.room&&res.room.code;
  if(code){
    if(sock&&res.room.me!=null&&res.room.me>=0)attach(sock,code,res.room.me);
    // anything that changed the table is pushed to the others
    if(res._l0!==undefined&&res._changed)broadcast(code,res._l0,res._c0,sock);
    schedule(code,res.due);}
  if(req.rid!=null)res.rid=req.rid;
  return strip(res);}
// note whether a request changed the room (compare stored versions around the call)
const handle0=core.handle;core.handle=async(st,req)=>{const c=req.code?String(req.code):'';
  const norm=c&&typeof normCode==='function'?normCode(c):c;const v0=norm?verOf(norm):0;const r=await handle0(st,req);
  if(r&&r.room&&r.room.code)r._changed=req.op==='create'||req.op==='join'||verOf(r.room.code)!==v0;return r;};

/* ---------- HTTP ---------- */
const CORS={'Access-Control-Allow-Origin':'*','Access-Control-Allow-Headers':'Content-Type','Access-Control-Allow-Methods':'POST, GET, OPTIONS'};
const server=http.createServer((rq,rs)=>{
  if(rq.method==='OPTIONS'){rs.writeHead(204,CORS);rs.end();return;}
  if(rq.url==='/health'){rs.writeHead(200,Object.assign({'Content-Type':'text/plain'},CORS));rs.end('ok '+store._m.size);return;}
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
