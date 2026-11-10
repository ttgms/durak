(()=>{
"use strict";
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

if(typeof module!=='undefined')module.exports={Game,SUITS,RANKS,R24,R36,R52,isJ,makeRng};

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

if(typeof module!=='undefined'){module.exports={aiMove,heuristicMove,PERSONAS,STYLES};}

// Card faces, back and opponent portraits, all as inline SVG strings.
const RED={h:1,d:1};
const SUIT_NAME={s:'пики',c:'трефы',h:'черви',d:'бубны'};
function suitShape(s,x,y,size,rot,fillOverride){
  const k=size/10,c=fillOverride||(RED[s]?'var(--red)':'var(--black)');
  const t=`translate(${x-size/2} ${y-size/2}) ${rot?`rotate(180 ${size/2} ${size/2})`:''} scale(${k})`;
  if(s==='h')return `<path transform="${t}" fill="${c}" d="M5 9.6C1.2 6.6 0 4.6 0 2.9 0 1.2 1.3 0 2.8 0 3.8 0 4.6.6 5 1.5 5.4.6 6.2 0 7.2 0 8.7 0 10 1.2 10 2.9 10 4.6 8.8 6.6 5 9.6Z"/>`;
  if(s==='d')return `<path transform="${t}" fill="${c}" d="M5 0 9 5 5 10 1 5Z"/>`;
  if(s==='s')return `<path transform="${t}" fill="${c}" d="M5 0C6.2 2.2 10 4.1 10 6.6 10 8.1 8.9 9 7.7 9 6.9 9 6.1 8.6 5.6 8 5.8 9 6.3 9.6 7.1 10H2.9C3.7 9.6 4.2 9 4.4 8 3.9 8.6 3.1 9 2.3 9 1.1 9 0 8.1 0 6.6 0 4.1 3.8 2.2 5 0Z"/>`;
  return `<g transform="${t}" fill="${c}"><circle cx="5" cy="2.6" r="2.4"/><circle cx="2.5" cy="6.1" r="2.4"/><circle cx="7.5" cy="6.1" r="2.4"/><circle cx="5" cy="5.4" r="1.4"/><path d="M4.4 6 5.6 6 6.6 10H3.4Z"/></g>`;
}
const PIPS={
 '2':[[50,30],[50,110]],
 '3':[[50,30],[50,70],[50,110]],
 '4':[[30,32],[70,32],[30,108],[70,108]],
 '5':[[30,32],[70,32],[50,70],[30,108],[70,108]],
 '6':[[30,32],[70,32],[30,70],[70,70],[30,108],[70,108]],
 '7':[[30,32],[70,32],[50,51],[30,70],[70,70],[30,108],[70,108]],
 '8':[[30,32],[70,32],[50,51],[30,70],[70,70],[50,89],[30,108],[70,108]],
 '9':[[30,30],[70,30],[30,56],[70,56],[50,70],[30,84],[70,84],[30,110],[70,110]],
 '10':[[30,30],[70,30],[50,43],[30,56],[70,56],[30,84],[70,84],[50,97],[30,110],[70,110]]
};
function hat(r,col){
  if(r==='К')return `<path d="M33 52 36 36 43 46 50 32 57 46 64 36 67 52Z" fill="#e6b450" stroke="#8a5d16" stroke-width="1.4" stroke-linejoin="round"/><circle cx="50" cy="31" r="2.6" fill="${col}"/><rect x="33" y="50" width="34" height="5" rx="1.5" fill="${col}"/>`;
  if(r==='Д')return `<path d="M31 55C31 38 40 30 50 30S69 38 69 55Z" fill="${col}"/><path d="M35 53C36 41 42 35 50 35S64 41 65 53" fill="none" stroke="#e6b450" stroke-width="2"/><g fill="#fff3d6"><circle cx="50" cy="40" r="2.2"/><circle cx="42" cy="44" r="1.6"/><circle cx="58" cy="44" r="1.6"/></g>`;
  return `<path d="M35 54C35 41 41 35 50 35S65 41 65 54Z" fill="${col}"/><rect x="32" y="50" width="36" height="7" rx="3" fill="#7a5236"/><circle cx="50" cy="34" r="3" fill="#e6b450"/>`;
}
function jokerSVG(c){const red=c.s==='r',a=red?'#c2272d':'#1d1d26',b=red?'#e6b450':'#6b6b78',d=red?'#2f7a46':'#3a3a46';
  const letters='ДЖОКЕР'.split('').map((ch,i)=>`<text x="10" y="${20+i*12}" text-anchor="middle" font-family="PT Serif,serif" font-weight="700" font-size="11" fill="${a}">${ch}</text>`).join('');
  return `<svg viewBox="0 0 100 140" aria-hidden="true"><rect x=".5" y=".5" width="99" height="139" rx="8" fill="#fbf7ee" stroke="#d9cfb8"/>${letters}<g transform="rotate(180 50 70)">${letters}</g>`+
   `<g transform="translate(22 30) scale(1.4)"><path d="M10 26 2 6l11 6 7-10 7 10 11-6-8 20z" fill="${a}"/><path d="M20 2l7 10 11-6-8 20H20z" fill="${d}"/><circle cx="2" cy="6" r="3" fill="${b}"/><circle cx="38" cy="6" r="3" fill="${b}"/><circle cx="20" cy="2" r="3" fill="${b}"/>`+
   `<ellipse cx="20" cy="36" rx="11" ry="12" fill="#f1cfa0"/><rect x="8" y="24" width="24" height="5" rx="2.5" fill="${b}"/><circle cx="16" cy="35" r="1.5" fill="#2b1d16"/><circle cx="24" cy="35" r="1.5" fill="#2b1d16"/><path d="M14 40c3 4 9 4 12 0" stroke="#7a3b2e" stroke-width="1.6" fill="none" stroke-linecap="round"/><circle cx="12" cy="39" r="2.2" fill="#e8908a" opacity=".6"/><circle cx="28" cy="39" r="2.2" fill="#e8908a" opacity=".6"/></g></svg>`;}
// faceSVG, backSVG and the card designs live in deco.js
// opponent portraits (40x40 viewBox)
const PORTRAITS={
  kuzmich:`<svg viewBox="0 0 40 40" aria-hidden="true"><path d="M8 17c0-8 5-12 12-12s12 4 12 12" fill="#7a4a2a"/><ellipse cx="20" cy="20" rx="10" ry="11" fill="#f1cfa0"/><path d="M8 14h24l-2 4H10z" fill="#b8312f"/><circle cx="16" cy="19" r="1.4" fill="#2b1d16"/><circle cx="24" cy="19" r="1.4" fill="#2b1d16"/><path d="M11 23c2 9 16 9 18 0-3 3-6 3-9 3s-6 0-9-3z" fill="#e8e1d6"/><path d="M16 25c2 1.5 6 1.5 8 0" stroke="#7a5a44" stroke-width="1.2" fill="none" stroke-linecap="round"/></svg>`,
  nura:`<svg viewBox="0 0 40 40" aria-hidden="true"><path d="M5 30C5 12 11 4 20 4s15 8 15 26l-4 3c-1-9-5-12-11-12S10 24 9 33Z" fill="#c8323a"/><g fill="#fbe7c8"><circle cx="11" cy="14" r="1.3"/><circle cx="20" cy="8" r="1.3"/><circle cx="29" cy="14" r="1.3"/><circle cx="8" cy="23" r="1.3"/><circle cx="32" cy="23" r="1.3"/></g><ellipse cx="20" cy="22" rx="9" ry="10" fill="#f0c99a"/><path d="M12 17c3-4 13-4 16 0-3-1.5-13-1.5-16 0z" fill="#d9d4cc"/><circle cx="16.5" cy="21" r="1.3" fill="#2b1d16"/><circle cx="23.5" cy="21" r="1.3" fill="#2b1d16"/><circle cx="13.5" cy="25" r="2" fill="#e8908a" opacity=".6"/><circle cx="26.5" cy="25" r="2" fill="#e8908a" opacity=".6"/><path d="M16.5 27c2 2 5 2 7 0" stroke="#7a3b2e" stroke-width="1.3" fill="none" stroke-linecap="round"/><path d="M14 31l6 3 6-3-2 6h-8z" fill="#c8323a"/></svg>`,
  kupets:`<svg viewBox="0 0 40 40" aria-hidden="true"><path d="M9 14c0-7 5-10 11-10s11 3 11 10z" fill="#3b2a1f"/><rect x="8" y="12" width="24" height="4" rx="2" fill="#6d4c33"/><ellipse cx="20" cy="21" rx="9" ry="9.5" fill="#efc596"/><circle cx="16" cy="20" r="1.3" fill="#2b1d16"/><circle cx="24" cy="20" r="1.3" fill="#2b1d16"/><path d="M14 17.5l4 .8M26 17.5l-4 .8" stroke="#3b2a1f" stroke-width="1.2" stroke-linecap="round"/><path d="M11 23c0 9 4 14 9 14s9-5 9-14c-2 3-5 4-9 4s-7-1-9-4z" fill="#5a3a24"/><path d="M15.5 25.5c3 1.4 6 1.4 9 0" stroke="#efc596" stroke-width="1.4" fill="none" stroke-linecap="round"/><circle cx="31" cy="30" r="3.2" fill="#e6b450" stroke="#8a5d16" stroke-width=".8"/><text x="31" y="31.6" font-size="4.4" text-anchor="middle" fill="#8a5d16" font-family="sans-serif" font-weight="700">₽</text></svg>`,
  you:`<svg viewBox="0 0 40 40" aria-hidden="true"><ellipse cx="20" cy="18" rx="8.5" ry="9.5" fill="#f1cfa0"/><path d="M11 15c0-6 4-9 9-9s9 3 9 9c-3-3-6-4-9-4s-6 1-9 4z" fill="#a5672f"/><circle cx="16.5" cy="18" r="1.2" fill="#2b1d16"/><circle cx="23.5" cy="18" r="1.2" fill="#2b1d16"/><path d="M17 22.5c2 1.5 4 1.5 6 0" stroke="#7a5a44" stroke-width="1.2" fill="none" stroke-linecap="round"/><path d="M6 40c0-8 6-12 14-12s14 4 14 12z" fill="#2e5a8c"/></svg>`
};

// Card designs (faces and backs) and table decoration. Everything is drawn as SVG in code.
/* ===================== card faces ===================== */
const FACE_STYLES={
  classic:{bg:'#fbf7ee',edge:'#d9cfb8',col:{h:'var(--red)',d:'var(--red)',s:'var(--black)',c:'var(--black)'},font:'PT Serif,Georgia,serif',court:'classic'},
  four:{bg:'#fbf7ee',edge:'#d9cfb8',col:{h:'#c2272d',d:'#1f62c4',s:'#1d1d26',c:'#23803e'},font:'PT Serif,Georgia,serif',court:'classic'},
  big:{bg:'#fbf7ee',edge:'#d9cfb8',col:{h:'var(--red)',d:'var(--red)',s:'var(--black)',c:'var(--black)'},font:'PT Serif,Georgia,serif',court:'classic',big:true},
  russ:{bg:'#f6ead2',edge:'#b58b4c',frame:'#b8322c',frame2:'#c9a24e',col:{h:'#b8322c',d:'#b8322c',s:'#22252e',c:'#22252e'},font:'Yeseva One,PT Serif,serif',court:'russ'},
  lubok:{bg:'#f5ead0',edge:'#3b2a1a',frame:'#1d1813',frame2:'#e0a526',col:{h:'#d23026',d:'#d23026',s:'#1f3d8f',c:'#1f3d8f'},font:'Yeseva One,PT Serif,serif',court:'lubok',rays:true},
  night:{bg:'#262a33',edge:'#454c5a',col:{h:'#ff8577',d:'#ff8577',s:'#e3e8f2',c:'#e3e8f2'},font:'PT Serif,Georgia,serif',court:'classic',courtBg:'#323846',dark:true},
  skaz:{bg:'#fbf3e0',edge:'#c9a46a',frame:'#2f5fb3',frame2:'#d4a73c',col:{h:'#c2272d',d:'#c2272d',s:'#1f2a44',c:'#1f2a44'},font:'Yeseva One,PT Serif,serif',court:'skaz',rays:true,fire:true},
  gold:{bg:'#1d1913',edge:'#b7832a',frame:'#b7832a',frame2:'#5b4519',col:{h:'#f07a62',d:'#f07a62',s:'#e8bd5c',c:'#e8bd5c'},font:'Yeseva One,PT Serif,serif',court:'russ',dark:true}
};
let faceStyle='classic';
function setFaceStyle(id){faceStyle=FACE_STYLES[id]?id:'classic';}
const ROBE={h:'#b8322c',d:'#c8651e',s:'#26406e',c:'#2c6b3c'};
// a bust of a tsar, a tsaritsa or a bogatyr for the "Russian" decks (inside 18..82 x 24..116)
function russCourt(r,s,col,st){
  const robe=ROBE[s],skin='#f1cfa0',gold='#e2b04a',dk=st.dark;
  let g=`<rect x="18" y="24" width="64" height="92" rx="6" fill="${dk?'#2a241b':'#fff7e6'}" stroke="${st.frame2||col}" stroke-width="1.2"/>`;
  g+=`<path d="M24 116c0-20 11-30 26-30s26 10 26 30z" fill="${robe}"/>`; // shoulders
  g+=`<path d="M38 116c2-14 6-22 12-22s10 8 12 22" fill="none" stroke="${gold}" stroke-width="2"/>`;
  g+=`<g fill="${gold}">${[0,1,2,3].map(i=>`<circle cx="50" cy="${99+i*5}" r="1.4"/>`).join('')}</g>`;
  g+=`<ellipse cx="50" cy="64" rx="12" ry="13.5" fill="${skin}"/>`;
  g+=`<circle cx="45.5" cy="63" r="1.5" fill="#2b1d16"/><circle cx="54.5" cy="63" r="1.5" fill="#2b1d16"/><circle cx="43" cy="68" r="2" fill="#e8908a" opacity=".45"/><circle cx="57" cy="68" r="2" fill="#e8908a" opacity=".45"/>`;
  if(r==='К'){ // tsar: crown, grey beard, ermine collar
    g+=`<path d="M38 86c0-8 4-14 12-14s12 6 12 14c-3 5-7 8-12 8s-9-3-12-8z" fill="#d9d2c6"/><path d="M44 72c2 2 4 2 6 2s4 0 6-2" stroke="#9e958a" stroke-width="1.6" fill="none"/>`;
    g+=`<path d="M37 52 38 38l6 7 6-11 6 11 6-7 1 14z" fill="${gold}" stroke="#8a5d16" stroke-width="1"/><rect x="36" y="49" width="28" height="5" rx="2" fill="${robe}" stroke="#8a5d16" stroke-width=".8"/><circle cx="50" cy="33" r="2.4" fill="${col}"/>`;
    g+=`<path d="M30 96c6-4 12-5 20-5s14 1 20 5v5c-6-3-12-4-20-4s-14 1-20 4z" fill="#fbf7ee"/><g fill="#22252e">${[34,42,50,58,66].map(x=>`<rect x="${x-.8}" y="96" width="1.6" height="3"/>`).join('')}</g>`;
  }else if(r==='Д'){ // tsaritsa: kokoshnik with pearls, braids
    g+=`<path d="M36 70c-3 10-2 22 2 30M64 70c3 10 2 22-2 30" stroke="#8a5a2e" stroke-width="5" stroke-linecap="round" fill="none"/>`;
    g+=`<path d="M34 56C34 38 41 28 50 28s16 10 16 28c-4-3-10-5-16-5s-12 2-16 5z" fill="${robe}" stroke="${gold}" stroke-width="1.6"/>`;
    g+=`<path d="M39 50c1-9 5-15 11-15s10 6 11 15" fill="none" stroke="${gold}" stroke-width="1.4"/><g fill="#fff3d6">${[[50,33],[43,38],[57,38],[40,46],[60,46]].map(([x,y])=>`<circle cx="${x}" cy="${y}" r="1.6"/>`).join('')}</g>`;
    g+=`<path d="M46 72c2 1.6 6 1.6 8 0" stroke="#a5463b" stroke-width="1.4" fill="none" stroke-linecap="round"/>`;
  }else{ // bogatyr: pointed helmet, moustache, chain mail
    g+=`<path d="M37 58c0-12 5-22 13-26 8 4 13 14 13 26z" fill="#b9c0c9" stroke="#6d7580" stroke-width="1"/><path d="M50 32v-6" stroke="#6d7580" stroke-width="1.6"/><path d="M37 57h26" stroke="${gold}" stroke-width="3"/><path d="M50 57v9" stroke="#6d7580" stroke-width="2"/>`;
    g+=`<path d="M43 71c3-2 5-2 7 0 2-2 4-2 7 0" stroke="#7a4a2a" stroke-width="2" fill="none" stroke-linecap="round"/>`;
    g+=`<g fill="#9aa2ad">${[0,1,2].map(j=>[0,1,2,3,4,5].map(i=>`<circle cx="${36+i*5.6+(j%2)*2.8}" cy="${92+j*4.5}" r="1.4"/>`).join('')).join('')}</g>`;
  }
  return g;
}
// fairy-tale deck: every court card is one of the game's characters
const SKAZ={К:{h:'tsar',d:'kupets',s:'koschei',c:'ilya'},Д:{h:'nesmeyana',d:'varvara',s:'yaga',c:'aglaya'},В:{h:'vanka',d:'tishka',s:'bayun',c:'alesha'}};
const SKAZ_TINT={h:'#fbe0d8',d:'#fbe8cf',s:'#dde4f2',c:'#ddeedf'};
function skazCourt(r,s,col,st){const id=SKAZ[r][s],ch=typeof CHARS!=='undefined'&&CHARS[id];
  let g=`<path d="M18 116V40c0-10 14-16 32-16s32 6 32 16v76z" fill="${SKAZ_TINT[s]}" stroke="${st.frame2}" stroke-width="1.4"/>`;
  g+=`<path d="M22 112V41c0-7 12-12 28-12s28 5 28 12v71z" fill="none" stroke="${st.frame}" stroke-width=".7" stroke-dasharray="2 2"/>`;
  if(ch)g+=ch.pic.replace('<svg ','<svg x="20" y="30" width="60" height="60" ');
  g+=`<rect x="20" y="94" width="60" height="15" rx="3" fill="${col}"/><text x="50" y="105" text-anchor="middle" font-family="${st.font}" font-size="10" fill="#fbf3e0">${ch?ch.short:''}</text>`;
  return g;}
function lubokCourt(r,s,col,st){
  return `<rect x="18" y="24" width="64" height="92" rx="4" fill="${col}" stroke="${st.frame}" stroke-width="1.6"/><rect x="22" y="28" width="56" height="84" rx="3" fill="none" stroke="#f5ead0" stroke-width="1" stroke-dasharray="3 2"/>`+
    `<text x="50" y="76" text-anchor="middle" font-family="${st.font}" font-size="40" fill="#f5ead0">${r}</text>`+
    `<g transform="translate(50 96)">${[0,72,144,216,288].map(a=>`<ellipse rx="3.2" ry="6" cy="-6" fill="${st.frame2}" transform="rotate(${a})"/>`).join('')}<circle r="3" fill="#f5ead0"/></g>`+
    `<path d="M30 96c4-4 8-4 10 0M70 96c-4-4-8-4-10 0" stroke="#f5ead0" stroke-width="1.6" fill="none" stroke-linecap="round"/>`;}
function faceSVG(c,styleId){
  const st=FACE_STYLES[styleId||faceStyle]||FACE_STYLES.classic;
  if(c.r==='J'){let j=jokerSVG(c);if(st.bg!=='#fbf7ee')j=j.replace('fill="#fbf7ee" stroke="#d9cfb8"',`fill="${st.dark?'#f3e7cc':st.bg}" stroke="${st.edge}"`);return j;}
  const col=st.col[c.s];
  const sh=(x,y,size,rot)=>suitShape(c.s,x,y,size,rot,col);
  let body='';
  if(st.big){
    body=`<text x="54" y="96" text-anchor="middle" font-family="${st.font}" font-weight="700" font-size="${c.r==='10'?44:52}" fill="${col}">${c.r}</text>`+sh(54,116,22,false);
  }else if(PIPS[c.r])body=PIPS[c.r].map(([x,y])=>sh(x,y,15,y>75)).join('');
  else if(c.r==='Т'){
    if(st.fire)body=`<g transform="translate(50 64) scale(.86) translate(-50 -82)">${firebird()}</g>`+sh(50,112,13,false);
    else if(st.court==='russ'||st.rays){const g=st.frame2||'#c9a24e';
      body=`<g fill="none" stroke="${g}" stroke-width="1.3">${[0,45,90,135,180,225,270,315].map(a=>`<path transform="rotate(${a} 50 70)" d="M50 44c5 4 5 9 0 12-5-3-5-8 0-12z"/>`).join('')}</g><circle cx="50" cy="70" r="20" fill="none" stroke="${g}" stroke-width="1" stroke-dasharray="1.5 2.5"/>`+sh(50,70,30,false);}
    else body=`<circle cx="50" cy="70" r="27" fill="none" stroke="#e6b450" stroke-width="1.5" stroke-dasharray="2 3"/>`+sh(50,70,36,false);
  }else if(st.court==='russ')body=russCourt(c.r,c.s,col,st);
  else if(st.court==='skaz')body=skazCourt(c.r,c.s,col,st);
  else if(st.court==='lubok')body=lubokCourt(c.r,c.s,col,st);
  else body=`<rect x="18" y="24" width="64" height="92" rx="6" fill="${st.courtBg||'url(#court)'}" stroke="${col}" stroke-width="1.2"/>`+hat(c.r,col)+
    `<text x="50" y="94" text-anchor="middle" font-family="Yeseva One,PT Serif,serif" font-size="34" fill="${col}">${c.r}</text>`+sh(50,106,10,false);
  const fs=st.big?(c.r==='10'?20:24):(c.r==='10'?15:17);
  const idx=(x,y,rot)=>`<g ${rot?'transform="rotate(180 50 70)"':''}><text x="${x}" y="${y}" text-anchor="middle" font-family="${st.font}" font-weight="700" font-size="${fs}" fill="${col}">${c.r}</text>${sh(x,y+(st.big?13:10),st.big?13:9,false)}</g>`;
  const frame=st.frame?`<rect x="4" y="4" width="92" height="132" rx="6" fill="none" stroke="${st.frame}" stroke-width=".8"/><rect x="6.5" y="6.5" width="87" height="127" rx="5" fill="none" stroke="${st.frame2}" stroke-width=".6" stroke-dasharray="2 2"/>`:'';
  return `<svg viewBox="0 0 100 140" aria-hidden="true"><rect x=".5" y=".5" width="99" height="139" rx="8" fill="${st.bg}" stroke="${st.edge}"/>${frame}`+
    idx(st.big?13:11,st.big?22:18,false)+(st.big?'':idx(11,18,true))+body+`</svg>`;
}

/* ===================== card backs ===================== */
const r2=n=>Math.round(n*100)/100;
function petal(cx,cy,len,w,ang,fill,extra){return `<ellipse cx="${cx}" cy="${r2(cy-len/2)}" rx="${w}" ry="${r2(len/2)}" fill="${fill}" transform="rotate(${ang} ${cx} ${cy})" ${extra||''}/>`;}
function ring(cx,cy,rad,n,fn){let s='';for(let i=0;i<n;i++){const a=i*Math.PI*2/n;s+=fn(r2(cx+Math.cos(a)*rad),r2(cy+Math.sin(a)*rad),r2(a*180/Math.PI),i);}return s;}
function corners(fn){return [[14,16,0],[86,16,90],[86,124,180],[14,124,270]].map(([x,y,a])=>`<g transform="translate(${x} ${y}) rotate(${a})">${fn()}</g>`).join('');}
function base(bg,inner){return `<rect width="100" height="140" rx="8" fill="#fbf7ee"/><rect x="4" y="4" width="92" height="132" rx="5" fill="${bg}"/>${inner}`;}
// Gzhel rose: cobalt bloom with white brush strokes
function gzRose(cx,cy,r,c){return `<circle cx="${cx}" cy="${cy}" r="${r}" fill="${c}"/>`+
  [.78,.56,.34].map((k,i)=>`<path d="M${r2(cx-r*k)} ${r2(cy+r*k*.15)}A${r2(r*k)} ${r2(r*k)} 0 0 1 ${r2(cx+r*k)} ${r2(cy+r*k*.15)}" stroke="#fff" stroke-width="${r2(r*(.13-i*.025))}" fill="none" stroke-linecap="round"/>`).join('')+
  `<circle cx="${cx}" cy="${r2(cy+r*.25)}" r="${r2(r*.16)}" fill="#fff"/>`;}
function gzLeaf(cx,cy,ang,c){return `<g transform="rotate(${ang} ${cx} ${cy})"><path d="M${cx} ${cy}c-5-4-5-12 0-16 5 4 5 12 0 16z" fill="${c}"/><path d="M${cx} ${cy-2}v-11" stroke="#fff" stroke-width=".8"/></g>`;}
// Khokhloma: rowan berries and golden grass curls
function curl(x,y,s,a,c){return `<path transform="translate(${x} ${y}) rotate(${a}) scale(${s})" d="M0 0c4-6 12-6 12 0 0 4-5 5-6 2s3-3 3-1" stroke="${c}" stroke-width="1.3" fill="none" stroke-linecap="round"/>`;}
function berry(x,y,r){return `<circle cx="${x}" cy="${y}" r="${r}" fill="#d4282e"/><circle cx="${r2(x-r*.35)}" cy="${r2(y-r*.35)}" r="${r2(r*.28)}" fill="#ff8a7a" opacity=".8"/>`;}
function goldLeaf(x,y,a,s){return `<g transform="translate(${x} ${y}) rotate(${a}) scale(${s})"><path d="M0 0c-4-5-3-12 0-15 3 3 4 10 0 15z" fill="#e2b04a"/><path d="M0-1v-12" stroke="#7a5212" stroke-width=".6"/></g>`;}
// a layered rose for Gorodets / Zhostovo
function kupavka(x,y,r,c,c2){return `<circle cx="${x}" cy="${y}" r="${r}" fill="${c}"/><path d="M${r2(x-r)} ${y}a${r} ${r} 0 0 0 ${r*2} 0" fill="${c2}"/>`+
  `<path d="M${r2(x-r*.7)} ${r2(y-r*.15)}a${r2(r*.7)} ${r2(r*.55)} 0 0 1 ${r2(r*1.4)} 0" stroke="#fff" stroke-width="${r2(r*.12)}" fill="none" stroke-linecap="round"/>`+
  `<path d="M${r2(x-r*.4)} ${r2(y+r*.25)}a${r2(r*.4)} ${r2(r*.3)} 0 0 1 ${r2(r*.8)} 0" stroke="#fff" stroke-width="${r2(r*.1)}" fill="none" stroke-linecap="round"/>`+
  ring(x,y,r*1.15,8,(px,py)=>`<circle cx="${px}" cy="${py}" r="${r2(r*.08)}" fill="#fff"/>`);}
function rose(x,y,r,c,hi){return `<circle cx="${x}" cy="${y}" r="${r}" fill="${c}"/>`+
  ring(x,y,r*.55,5,(px,py)=>`<circle cx="${px}" cy="${py}" r="${r2(r*.42)}" fill="${hi}" opacity=".55"/>`)+`<circle cx="${x}" cy="${y}" r="${r2(r*.35)}" fill="${c}"/><path d="M${r2(x-r*.25)} ${y}a${r2(r*.25)} ${r2(r*.2)} 0 0 1 ${r2(r*.5)} 0" stroke="${hi}" stroke-width="${r2(r*.1)}" fill="none"/>`;}
function leaf(x,y,a,s,c,vein){return `<g transform="translate(${x} ${y}) rotate(${a}) scale(${s})"><path d="M0 0c-5-4-6-12 0-17 6 5 5 13 0 17z" fill="${c}"/><path d="M0-1v-14" stroke="${vein}" stroke-width=".7"/></g>`;}
// a firebird for Palekh
function firebird(){const g='#e2b04a';
  return `<g fill="none" stroke="${g}" stroke-width="1.2" stroke-linecap="round">`+
    [[-38,0],[-20,4],[0,8],[20,4],[38,0]].map(([a,o])=>`<path transform="rotate(${a} 50 78)" d="M50 78c-2 14 2 30 ${o} 44"/>`).join('')+`</g>`+
    [[-38],[-20],[0],[20],[38]].map(([a])=>`<g transform="rotate(${a} 50 78)"><circle cx="50" cy="114" r="3.4" fill="#d4282e" stroke="${g}" stroke-width="1"/><circle cx="50" cy="114" r="1.2" fill="${g}"/></g>`).join('')+
    `<path d="M50 80c-9 0-14-6-13-13 6 1 10 4 13 9 3-5 7-8 13-9 1 7-4 13-13 13z" fill="${g}"/>`+ // wings
    `<path d="M50 84c-5-3-6-12 0-20 6 8 5 17 0 20z" fill="#d4282e" stroke="${g}" stroke-width="1"/>`+ // body
    `<circle cx="50" cy="60" r="4.5" fill="${g}"/><path d="M50 56c-1-5 0-9 2-11M50 56c-3-4-5-7-5-10M50 56c2-3 5-6 7-6" stroke="${g}" stroke-width="1" fill="none"/><circle cx="51.3" cy="59.5" r=".9" fill="#1d1913"/><path d="M54 61l4 1-4 1z" fill="#d4282e"/>`;}
function crown(x,y,s,c,c2){return `<g transform="translate(${x} ${y}) scale(${s})"><path d="M-14 8-15-8l7 6 8-11 8 11 7-6-1 16z" fill="${c}" stroke="${c2}" stroke-width="1"/><rect x="-15" y="6" width="30" height="5" rx="2" fill="${c}" stroke="${c2}" stroke-width="1"/><circle cx="0" cy="-12" r="2.2" fill="#d4282e"/><circle cx="-15" cy="-9" r="1.6" fill="${c}"/><circle cx="15" cy="-9" r="1.6" fill="${c}"/></g>`;}
// a Mezen horse: graphic, two colours
function horse(x,y,s,c,c2){return `<g transform="translate(${x} ${y}) scale(${s})"><path d="M-10 0c0-5 4-7 9-7h7l4-6 3 1-2 7c1 2 0 5-2 6H-6c-3 0-4-1-4-1z" fill="${c}"/><path d="M-8 1v8M-3 1v8M5 1v8M9 0v8" stroke="${c}" stroke-width="1.6"/><path d="M-10 -1c-4-1-6 2-7 6" stroke="${c}" stroke-width="1.4" fill="none"/><path d="M-6-4h12M-6-1h12" stroke="${c2}" stroke-width=".8"/><circle cx="10" cy="-10" r=".8" fill="${c2}"/></g>`;}
function bird(x,y,s,c){return `<g transform="translate(${x} ${y}) scale(${s})"><path d="M-6 0c0-4 4-6 8-5l3-3 2 1-2 3c2 2 1 6-2 7h-6c-2 0-3-1-3-3z" fill="${c}"/><path d="M-6-1c-3-2-4-4-4-6M-6 0c-4-1-5-3-6-4" stroke="${c}" stroke-width="1" fill="none"/><path d="M-1 3v3M2 3v3" stroke="${c}" stroke-width=".9"/></g>`;}
// a matryoshka doll, about 28 x 46 at scale 1, centred on its waist
function matr(x,y,s,c,sc){return `<g transform="translate(${x} ${y}) scale(${s})">`+
  `<path d="M0-23c-7 0-10 5-10 11 0 3 1 5 2 7-4 4-6 9-6 15 0 9 6 13 14 13s14-4 14-13c0-6-2-11-6-15 1-2 2-4 2-7 0-6-3-11-10-11z" fill="${c}" stroke="#3a1a10" stroke-width=".7"/>`+
  `<ellipse cx="0" cy="-11" rx="6.2" ry="6" fill="#f6dcc0"/><path d="M-6.2-12c1-4 4-5 6.2-5s5.2 1 6.2 5c-2-1.6-4-2.2-6.2-2.2s-4.2.6-6.2 2.2z" fill="#6b3a1c"/>`+
  `<path d="M-7.6-10c0-7 3.4-9.6 7.6-9.6s7.6 2.6 7.6 9.6" fill="none" stroke="${sc}" stroke-width="1.5"/>`+
  `<circle cx="-2.2" cy="-11" r=".8" fill="#2b1d16"/><circle cx="2.2" cy="-11" r=".8" fill="#2b1d16"/><circle cx="-3.6" cy="-8.6" r="1.3" fill="#e8605a" opacity=".6"/><circle cx="3.6" cy="-8.6" r="1.3" fill="#e8605a" opacity=".6"/><ellipse cx="0" cy="-7.6" rx="1" ry=".7" fill="#c2272d"/>`+
  `<ellipse cx="0" cy="11" rx="8.6" ry="10" fill="#fbf3e0"/>`+
  `<path d="M0 13c-4-1-6 1-7 4M0 13c4-1 6 1 7 4" stroke="#2f7a46" stroke-width="1.4" fill="none"/>`+
  `<circle cx="0" cy="9" r="4" fill="${sc}"/><circle cx="0" cy="9" r="1.6" fill="#ffe09a"/>`+
  `<g fill="${sc}"><circle cx="-4" cy="3" r="1.1"/><circle cx="4" cy="3" r="1.1"/></g></g>`;}
const BACK_ART={
  gzhel:()=>base('#f3f6fd',
    `<rect x="7" y="7" width="86" height="126" rx="4" fill="none" stroke="#1e4aa8" stroke-width="2"/><rect x="10" y="10" width="80" height="120" rx="3" fill="none" stroke="#1e4aa8" stroke-width=".7"/>`+
    `<g fill="#1e4aa8">${[...Array(13)].map((_,i)=>`<circle cx="${14+i*6}" cy="13.5" r="1"/><circle cx="${14+i*6}" cy="126.5" r="1"/>`).join('')}</g>`+
    ring(50,70,25,10,(x,y,a)=>gzLeaf(x,y,a+90,'#1e4aa8'))+gzRose(50,70,13,'#1e4aa8')+
    ring(50,70,34,16,(x,y)=>`<circle cx="${x}" cy="${y}" r="1.3" fill="#1e4aa8"/>`)+
    corners(()=>gzRose(0,0,5,'#1e4aa8')+gzLeaf(0,0,135,'#3d6ad1'))),
  hohloma:()=>base('#151113',
    `<rect x="7" y="7" width="86" height="126" rx="4" fill="none" stroke="#c9952f" stroke-width="1.3"/>`+
    [...Array(10)].map((_,i)=>curl(12+(i%5)*17,i<5?18:122,.75,i<5?0:180,'#c9952f')).join('')+
    [[30,62,-50],[70,62,50],[34,88,-130],[66,88,130],[50,52,0],[50,96,180]].map(([x,y,a])=>goldLeaf(x,y,a,1.15)).join('')+
    `<path d="M50 70c-14-8-22-2-24 10M50 70c14-8 22-2 24 10M50 70v26" stroke="#c9952f" stroke-width="1.3" fill="none"/>`+
    [[50,66,5],[44,73,4.2],[56,73,4.2],[50,78,3.8],[41,64,3.4],[59,64,3.4],[47,58,3],[53,58,3]].map(([x,y,r])=>berry(x,y,r)).join('')+
    corners(()=>berry(0,0,2.6)+goldLeaf(3,3,135,.6))),
  gorodets:()=>base('#ecbc4c',
    `<rect x="7" y="7" width="86" height="126" rx="4" fill="none" stroke="#6b3412" stroke-width="2.4"/><g fill="#fff">${[...Array(11)].map((_,i)=>`<circle cx="${15+i*7}" cy="7" r="1"/><circle cx="${15+i*7}" cy="133" r="1"/>`).join('')}</g>`+
    [[30,56,-40],[70,56,40],[28,86,-140],[72,86,140],[50,98,180],[50,42,0]].map(([x,y,a])=>leaf(x,y,a,1.2,'#2f7a46','#cfe9d6')).join('')+
    kupavka(50,70,13,'#2f5fb3','#1f3f80')+kupavka(31,72,7,'#d23a2c','#9d2219')+kupavka(69,72,7,'#d23a2c','#9d2219')+
    corners(()=>kupavka(0,0,4.5,'#d23a2c','#9d2219'))),
  zhostovo:()=>base('#121214',
    `<rect x="8" y="8" width="84" height="124" rx="4" fill="none" stroke="#c9952f" stroke-width="1" stroke-dasharray="3 2"/><rect x="11" y="11" width="78" height="118" rx="3" fill="none" stroke="#c9952f" stroke-width=".5"/>`+
    [[34,58,-60],[66,58,60],[30,84,-120],[70,84,120],[44,94,-160],[56,94,160],[50,46,0]].map(([x,y,a])=>leaf(x,y,a,1.1,'#2f6d45','#7fb88f')).join('')+
    rose(50,68,10,'#d8506d','#f7b6c4')+rose(36,74,7,'#f4ecdc','#ffffff')+rose(64,74,7,'#efa92e','#ffe09a')+
    [[38,52],[62,52],[24,70],[76,70],[38,96],[62,96]].map(([x,y])=>`<g fill="#7aa6e8">${ring(x,y,2,5,(a,b)=>`<circle cx="${a}" cy="${b}" r="1.3"/>`)}</g><circle cx="${x}" cy="${y}" r="1" fill="#ffe09a"/>`).join('')+
    corners(()=>`<path d="M-2 6c0-6 2-8 8-8" stroke="#c9952f" stroke-width="1" fill="none"/><circle cx="0" cy="0" r="1.5" fill="#c9952f"/>`)),
  palekh:()=>base('#0f0d10',
    `<rect x="7" y="7" width="86" height="126" rx="4" fill="none" stroke="#c9952f" stroke-width="1"/><g fill="#c9952f">${[...Array(12)].map((_,i)=>`<circle cx="${13+i*6.7}" cy="11" r=".7"/><circle cx="${13+i*6.7}" cy="129" r=".7"/>`).join('')}</g>`+
    `<g transform="translate(0 -6)">${firebird()}</g>`+corners(()=>`<path d="M0 0c3-3 7-3 9 0-2 3-6 3-9 0z" fill="#c9952f"/>`)),
  tsar:()=>base('#6e0d1c',
    `<g opacity=".35" fill="#e2b04a">${[...Array(5)].map((_,i)=>[...Array(7)].map((_,j)=>i===4&&j%2?'':`<path d="M${14+i*18+(j%2)*9} ${12+j*19}l3 5-3 5-3-5z"/>`).join('')).join('')}</g>`+
    `<rect x="7" y="7" width="86" height="126" rx="4" fill="none" stroke="#e2b04a" stroke-width="2"/><rect x="11" y="11" width="78" height="118" rx="3" fill="none" stroke="#e2b04a" stroke-width=".8"/>`+
    `<circle cx="50" cy="70" r="20" fill="#4a0712" stroke="#e2b04a" stroke-width="1.5"/>`+ring(50,70,23,20,(x,y)=>`<circle cx="${x}" cy="${y}" r="1" fill="#e2b04a"/>`)+crown(50,72,1,'#e2b04a','#8a5d16')),
  mezen:()=>base('#efe0c0',
    `<rect x="7" y="7" width="86" height="126" rx="3" fill="none" stroke="#1d1813" stroke-width="1"/>`+
    `<path d="${[...Array(14)].map((_,i)=>`M${10+i*6} 14l3-4 3 4`).join('')}" stroke="#a3271c" stroke-width="1.2" fill="none"/><path d="${[...Array(14)].map((_,i)=>`M${10+i*6} 126l3 4 3-4`).join('')}" stroke="#a3271c" stroke-width="1.2" fill="none"/>`+
    `<path d="M10 20h80M10 120h80M10 46h80M10 94h80" stroke="#1d1813" stroke-width=".8"/>`+
    [24,42,60,78].map((x,i)=>bird(x,33,1,i%2?'#1d1813':'#a3271c')).join('')+horse(50,74,1.7,'#a3271c','#1d1813')+
    [24,42,60,78].map((x,i)=>bird(x,108,1,i%2?'#a3271c':'#1d1813')).join('')),
  pavlov:()=>base('#141013',
    `<rect x="7" y="7" width="86" height="126" rx="4" fill="none" stroke="#c8202e" stroke-width="2"/>`+
    `<path d="${[...Array(13)].map((_,i)=>`M${10+i*6.2} 12l3.1 3 3.1-3`).join('')}" stroke="#2f7a46" stroke-width="1.1" fill="none"/><path d="${[...Array(13)].map((_,i)=>`M${10+i*6.2} 128l3.1-3 3.1 3`).join('')}" stroke="#2f7a46" stroke-width="1.1" fill="none"/>`+
    `<path d="M14 70h72M50 30v80" stroke="#e2b04a" stroke-width=".5" stroke-dasharray="1 3" opacity=".6"/>`+
    [[34,52,-50],[66,52,50],[30,90,-130],[70,90,130],[50,44,0],[50,98,180],[38,70,-90],[62,70,90]].map(([x,y,a])=>leaf(x,y,a,1.1,'#2f7a46','#9fd4a8')).join('')+
    rose(36,60,7,'#efa92e','#ffe09a')+rose(64,60,7,'#efa92e','#ffe09a')+rose(36,82,7,'#3a68c4','#a9c4f2')+rose(64,82,7,'#3a68c4','#a9c4f2')+rose(50,71,12,'#c8202e','#f58a90')+
    corners(()=>rose(0,0,4.6,'#c8202e','#f58a90')+leaf(4,4,135,.55,'#2f7a46','#9fd4a8'))),
  matr:()=>base('#e8b528',
    `<rect x="7" y="7" width="86" height="126" rx="4" fill="none" stroke="#b8222a" stroke-width="2.4"/>`+
    `<g fill="#b8222a">${[...Array(12)].map((_,i)=>`<circle cx="${14+i*6.6}" cy="15" r="1.6"/><circle cx="${14+i*6.6}" cy="125" r="1.6"/>`).join('')}</g>`+
    `<g fill="#2f7a46">${[...Array(11)].map((_,i)=>`<circle cx="${17.3+i*6.6}" cy="15" r=".9"/><circle cx="${17.3+i*6.6}" cy="125" r=".9"/>`).join('')}</g>`+
    matr(22,82,.86,'#2f5fb3','#d23026')+matr(78,82,.86,'#2f7a46','#d23026')+matr(50,74,1.45,'#c8202e','#2f5fb3')),
  boyar:()=>base('#3b1030',
    `<rect x="6" y="6" width="88" height="128" rx="5" fill="none" stroke="#e6b450" stroke-width="2.2"/><rect x="11" y="11" width="78" height="118" rx="3" fill="none" stroke="#e6b450" stroke-width=".8" stroke-dasharray="1.5 2.5"/>`+
    `<g fill="#e6b450" opacity=".22">${[...Array(6)].map((_,r)=>[...Array(4)].map((_,c)=>`<path d="M${22+c*19} ${24+r*19}l3 4-3 4-3-4z"/>`).join('')).join('')}</g>`+
    `<circle cx="50" cy="70" r="24" fill="#3b1030" stroke="#e6b450" stroke-width="2"/><circle cx="50" cy="70" r="19" fill="none" stroke="#e6b450" stroke-width=".7" stroke-dasharray="2 2"/>`+
    `<path d="M35 77l-3-15 9 7 9-12 9 12 9-7-3 15z" fill="#e6b450"/><rect x="34" y="78" width="32" height="4" rx="1" fill="#e6b450"/><circle cx="50" cy="56" r="2.2" fill="#e6b450"/><circle cx="41" cy="73" r="1.6" fill="#c8202e"/><circle cx="50" cy="72" r="1.8" fill="#2f7a46"/><circle cx="59" cy="73" r="1.6" fill="#c8202e"/>`+
    corners(()=>`<path d="M0-5l1.6 3.4 3.4 1.6-3.4 1.6L0 5l-1.6-3.4L-5 0l3.4-1.6z" fill="#e6b450"/>`)),
  kruzhevo:()=>base('#1b2a55',
    `<g fill="none" stroke="#f3f0e8" stroke-width=".8">`+
      `<path d="${[...Array(15)].map((_,i)=>`M${7+i*6} 9a3 3 0 0 0 6 0`).join('')}"/><path d="${[...Array(15)].map((_,i)=>`M${7+i*6} 131a3 3 0 0 1 6 0`).join('')}"/>`+
      `<circle cx="50" cy="70" r="30"/><circle cx="50" cy="70" r="22"/><circle cx="50" cy="70" r="9"/></g>`+
    ring(50,70,26,18,(x,y)=>`<circle cx="${x}" cy="${y}" r="2.6" fill="none" stroke="#f3f0e8" stroke-width=".8"/>`)+
    ring(50,70,15.5,8,(x,y,a)=>petal(x,y+4,9,2.6,a+90,'none','stroke="#f3f0e8" stroke-width=".8"'))+
    ring(50,70,34,24,(x,y)=>`<circle cx="${x}" cy="${y}" r=".9" fill="#f3f0e8"/>`)+
    `<g fill="#f3f0e8" opacity=".5">${[...Array(6)].map((_,i)=>[...Array(3)].map((_,j)=>`<circle cx="${16+i*13.6}" cy="${20+j*4}" r=".8"/><circle cx="${16+i*13.6}" cy="${112+j*4}" r=".8"/>`).join('')).join('')}</g>`+
    `<circle cx="50" cy="70" r="3" fill="#f3f0e8"/>`)
};
let backDefsDone=false;
function ensureBackDefs(){if(backDefsDone)return;backDefsDone=true;
  const d=document.createElement('div');d.style.cssText='position:absolute;width:0;height:0;overflow:hidden';d.setAttribute('aria-hidden','true');
  d.innerHTML=`<svg width="0" height="0"><defs>${Object.keys(BACK_ART).map(k=>`<symbol id="bk_${k}" viewBox="0 0 100 140">${BACK_ART[k]()}</symbol>`).join('')}</defs></svg>`;
  document.body.appendChild(d);}
let backId='gzhel';
function backSVG(id){ensureBackDefs();const k=BACK_ART[id||backId]?(id||backId):'gzhel';return `<svg viewBox="0 0 100 140" aria-hidden="true"><use href="#bk_${k}"/></svg>`;}

/* ===================== table decoration ===================== */
// White shapes used as masks, so each table can tint them with its own thread colour.
const svgUrl=s=>`url("data:image/svg+xml;utf8,${encodeURIComponent(`<svg xmlns='http://www.w3.org/2000/svg' ${s}</svg>`)}")`;
const EMB={
  glass:`viewBox='0 0 200 200'><g fill='none' stroke='#fff' stroke-width='2'><circle cx='100' cy='100' r='90'/><circle cx='100' cy='100' r='84' stroke-dasharray='3 5'/></g><g fill='#fff'><path d='M72 70h56l-6 74H78z' opacity='.55'/><path d='M66 92h68v8h-6l-4 56c-1 6-5 9-10 9H86c-5 0-9-3-10-9l-4-56h-6z'/><path d='M134 104c16 0 18 30 0 32v-8c8-1 8-15 0-16z'/><rect x='70' y='170' width='60' height='6' rx='3'/></g><g fill='none' stroke='#fff' stroke-width='3' stroke-linecap='round'><path d='M88 60c-6-8 6-14 0-22M100 58c-6-8 6-14 0-24M112 60c-6-8 6-14 0-22'/></g><g fill='none' stroke='#fff' stroke-width='1.6' opacity='.9'><path d='M80 112h40M81 126h38M82 140h36'/></g>`,
  cherry:`viewBox='0 0 200 200'><g fill='#fff'><circle cx='72' cy='134' r='26'/><circle cx='130' cy='142' r='24'/><path d='M104 46c26-14 56-8 70 10-26 14-54 10-70-10z'/></g><g fill='none' stroke='#fff' stroke-width='4' stroke-linecap='round'><path d='M72 108c8-30 22-52 32-62M130 118c-4-30-12-54-26-72'/></g><g fill='none' stroke='#fff' stroke-width='2'><circle cx='100' cy='100' r='92' stroke-dasharray='1 7' stroke-linecap='round'/></g>`,
  snow:`viewBox='0 0 200 200'><g stroke='#fff' stroke-linecap='round' fill='none'>${[...Array(6)].map((_,i)=>`<g transform='rotate(${i*60} 100 100)'><path d='M100 100V14' stroke-width='5'/><path d='M100 44l-16-16M100 44l16-16M100 70l-22-20M100 70l22-20M100 24l-8-8M100 24l8-8' stroke-width='4'/></g>`).join('')}</g><circle cx='100' cy='100' r='14' fill='#fff'/><circle cx='100' cy='100' r='26' fill='none' stroke='#fff' stroke-width='2.5'/>`,
  rosette:`viewBox='0 0 200 200'><g fill='none' stroke='#fff' stroke-width='2'><circle cx='100' cy='100' r='92'/><circle cx='100' cy='100' r='84' stroke-dasharray='4 6'/><circle cx='100' cy='100' r='40'/></g><g fill='#fff'>${[0,1,2,3].map(i=>`<g transform='rotate(${i*90} 100 100)'>`+`<path d='M100 24c8 10 8 22 0 30-8-8-8-20 0-30z'/></g>`).join('')}${[...Array(24)].map((_,i)=>{const a=i*Math.PI/12;return `<circle cx='${r2(100+Math.cos(a)*62)}' cy='${r2(100+Math.sin(a)*62)}' r='3'/>`;}).join('')}<path d='M100 82c6 8 18 10 18 20 0 6-5 9-10 9-3 0-6-2-7-4 0 4 2 7 5 9h-12c3-2 5-5 5-9-1 2-4 4-7 4-5 0-10-3-10-9 0-10 12-12 18-20z'/></g>`,
  doily:`viewBox='0 0 200 200'><g fill='none' stroke='#fff' stroke-width='2.2'>${[...Array(24)].map((_,i)=>`<path transform='rotate(${i*15} 100 100)' d='M92 6a8 8 0 0 0 16 0'/>`).join('')}<circle cx='100' cy='100' r='88'/><circle cx='100' cy='100' r='64' stroke-dasharray='2 5'/><circle cx='100' cy='100' r='36'/></g><g fill='#fff'>${[...Array(16)].map((_,i)=>{const a=i*Math.PI/8;return `<circle cx='${r2(100+Math.cos(a)*76)}' cy='${r2(100+Math.sin(a)*76)}' r='5'/><circle cx='${r2(100+Math.cos(a+.2)*50)}' cy='${r2(100+Math.sin(a+.2)*50)}' r='2.6'/>`;}).join('')}</g>`,
  flower:`viewBox='0 0 200 200'><g fill='#fff'>${[...Array(8)].map((_,i)=>`<path transform='rotate(${i*45} 100 100)' d='M100 100c-14-20-14-44 0-60 14 16 14 40 0 60z'/>`).join('')}${[...Array(16)].map((_,i)=>`<path transform='rotate(${i*22.5+11} 100 100)' d='M100 34c-5-8-5-16 0-22 5 6 5 14 0 22z' opacity='.7'/>`).join('')}</g><circle cx='100' cy='100' r='16' fill='none' stroke='#fff' stroke-width='3'/><circle cx='100' cy='100' r='92' fill='none' stroke='#fff' stroke-width='2' stroke-dasharray='1 7' stroke-linecap='round'/>`,
  crown:`viewBox='0 0 200 200'><g fill='none' stroke='#fff' stroke-width='2'><circle cx='100' cy='100' r='90'/><circle cx='100' cy='100' r='82'/></g><g fill='#fff'>${[...Array(36)].map((_,i)=>{const a=i*Math.PI/18;return `<circle cx='${r2(100+Math.cos(a)*86)}' cy='${r2(100+Math.sin(a)*86)}' r='1.8'/>`;}).join('')}<path d='M64 118 60 72l20 18 20-34 20 34 20-18-4 46z'/><rect x='62' y='120' width='76' height='12' rx='4'/>${[-1,1].map(sgn=>[...Array(7)].map((_,i)=>`<ellipse transform='rotate(${sgn*(20+i*16)} 100 100)' cx='100' cy='${172-i*0}' rx='5' ry='10'/>`).join('')).join('')}</g>`
};
const DAMASK=svgUrl(`width='64' height='64'><g fill='#fff'><path d='M32 6c6 8 6 16 0 22-6-6-6-14 0-22zM32 58c-6-8-6-16 0-22 6 6 6 14 0 22zM6 32c8-6 16-6 22 0-6 6-14 6-22 0zM58 32c-8 6-16 6-22 0 6-6 14-6 22 0z'/><circle cx='32' cy='32' r='3'/><circle cx='0' cy='0' r='3'/><circle cx='64' cy='0' r='3'/><circle cx='0' cy='64' r='3'/><circle cx='64' cy='64' r='3'/></g>`);
const WOOD=svgUrl(`width='240' height='120'><defs><filter id='g'><feTurbulence type='fractalNoise' baseFrequency='.008 .25' numOctaves='3' seed='4'/><feColorMatrix values='0 0 0 0 .2  0 0 0 0 .1  0 0 0 0 .04  0 0 0 .55 0'/></filter></defs><rect width='240' height='120' fill='#8b5a33'/><rect width='240' height='120' filter='url(#g)'/><g fill='#000' opacity='.28'><rect y='0' width='240' height='2'/><rect y='40' width='240' height='2'/><rect y='80' width='240' height='2'/></g><g fill='#fff' opacity='.05'><rect y='2' width='240' height='6'/><rect y='42' width='240' height='6'/><rect y='82' width='240' height='6'/></g><g fill='#000' opacity='.25'><rect x='70' y='2' width='1.5' height='38'/><rect x='180' y='42' width='1.5' height='38'/><rect x='120' y='82' width='1.5' height='38'/></g>`);
const TABLE_DECO={ // emblem, its opacity, thread colour for the stitched border
  sukno:{emb:'rosette',op:.09,thread:'#efe0a8'},
  barhat:{emb:'flower',op:.08,thread:'#cdd9fa'},
  izba:{emb:'doily',op:.2,thread:'#f3e8d2'},
  yarmarka:{emb:'flower',op:.11,thread:'#ffd88a'},
  palaty:{emb:'crown',op:.12,thread:'#e6b450'},
  kupe:{emb:'glass',op:.06,thread:'#dfe3ea'},
  dacha:{emb:'cherry',op:.07,thread:'#fff1e0'},
  morozko:{emb:'snow',op:.08,thread:'#eef6ff'}
};
// table backgrounds shared by the table, the menus and the shop preview
const GINGHAM='linear-gradient(90deg,rgba(255,240,225,.13) 50%,transparent 50%) 0 0/34px 34px,linear-gradient(rgba(255,240,225,.13) 50%,transparent 50%) 0 0/34px 34px';
const TABLE_BG={sukno:'radial-gradient(#2a6b49,#0f3424)',barhat:'radial-gradient(#3352a0,#0f1c3d)',izba:'repeating-linear-gradient(0deg,#8a5a34 0 3px,#946239 3px 9px,#8d5d36 9px 14px)',
  yarmarka:'radial-gradient(#b23232,#4c1014)',palaty:'radial-gradient(#9a1c30,#300810)',kupe:'repeating-linear-gradient(90deg,rgba(255,255,255,.04) 0 2px,transparent 2px 9px),radial-gradient(#84483a,#2c1611)',
  dacha:GINGHAM+',radial-gradient(#9c3434,#4e1616)',morozko:'radial-gradient(#3d78b3,#0d2341)'};
(function injectTableCss(){
  let css=`.tdeco{position:absolute;inset:0;pointer-events:none;overflow:hidden}
.tdeco .emb{position:absolute;left:50%;top:50%;width:min(62vmin,420px);height:min(62vmin,420px);transform:translate(-50%,-52%);background:var(--thread);-webkit-mask:var(--emb) center/contain no-repeat;mask:var(--emb) center/contain no-repeat;opacity:var(--embop)}
.tdeco .stitch{position:absolute;inset:20px;border:2px dashed var(--thread);border-radius:24px;opacity:.28}
.tprev{position:relative;overflow:hidden}.tprev .tdeco .emb{width:64px;height:64px}.tprev .tdeco .stitch{inset:8px;border-width:1px;border-radius:8px}
.skin-palaty .tdeco .stitch{border:3px double var(--thread);opacity:.45}
.tdeco .damask{display:none;position:absolute;inset:0;background:var(--thread);-webkit-mask:${DAMASK} 0 0/64px 64px;mask:${DAMASK} 0 0/64px 64px;opacity:.07}
.skin-palaty .tdeco .damask{display:block}
.skin-izba{background:${WOOD} 0 0/240px 120px,#8b5a33!important}
.skin-barhat{background-image:linear-gradient(115deg,rgba(255,255,255,.07) 0,transparent 30%,rgba(255,255,255,.05) 55%,transparent 75%,rgba(255,255,255,.04) 100%),radial-gradient(ellipse at 50% 45%,rgba(255,255,255,.07),transparent 60%),radial-gradient(ellipse at 50% 50%,var(--felt) 0%,var(--felt2) 55%,var(--felt-deep) 100%)}
.skin-kupe{background-image:repeating-linear-gradient(90deg,rgba(255,255,255,.035) 0 2px,transparent 2px 9px),radial-gradient(ellipse at 50% 45%,rgba(255,235,210,.08),transparent 60%),radial-gradient(ellipse at 50% 50%,var(--felt) 0%,var(--felt2) 55%,var(--felt-deep) 100%)}
.skin-kupe .tdeco .stitch{border:2px solid var(--thread);opacity:.22;inset:16px;border-radius:14px}
.skin-dacha{background:radial-gradient(ellipse at 50% 50%,transparent 35%,rgba(30,5,5,.45) 100%),${GINGHAM},radial-gradient(ellipse at 50% 50%,var(--felt) 0%,var(--felt2) 60%,var(--felt-deep) 100%)!important}
.skin-dacha .tdeco .stitch{display:none}
.skin-morozko .tdeco .stitch{border-style:dotted;border-width:3px;opacity:.35}
.skin-morozko .tdeco::before{content:"";position:absolute;inset:0;background:radial-gradient(circle at 0 0,rgba(235,245,255,.22),transparent 28%),radial-gradient(circle at 100% 0,rgba(235,245,255,.18),transparent 26%),radial-gradient(circle at 0 100%,rgba(235,245,255,.16),transparent 24%),radial-gradient(circle at 100% 100%,rgba(235,245,255,.2),transparent 28%)}
.skin-palaty{background-image:radial-gradient(ellipse at 50% 50%,transparent 30%,rgba(0,0,0,.35) 100%),radial-gradient(ellipse at 50% 50%,var(--felt) 0%,var(--felt2) 55%,var(--felt-deep) 100%)}
`;
  for(const k in TABLE_DECO){const t=TABLE_DECO[k];css+=`.skin-${k}{--emb:${svgUrl(EMB[t.emb])};--embop:${t.op};--thread:${t.thread}}\n`;}
  const st=document.createElement('style');st.textContent=css;document.head.appendChild(st);
})();
const TDECO_HTML='<div class="tdeco" aria-hidden="true"><div class="damask"></div><div class="emb"></div><div class="stitch"></div></div>';

/* ===================== living menu background ===================== */
// A few slow, faint particles behind the main menu, matched to the chosen table.
// Runs only while the menu is visible and the tab is in front; ~30 fps.
const menuFx=(function(){
  let cv=null,ctx=null,parts=[],kind='sukno',raf=0,last=0,want=false,W=0,H=0,dpr=1;
  const rnd=(a,b)=>a+Math.random()*(b-a),pick=a=>a[Math.floor(Math.random()*a.length)];
  const evening=()=>{const h=new Date().getHours();return h>=20||h<6;};
  const COUNT={sukno:9,barhat:14,izba:12,yarmarka:12,palaty:11,kupe:6,dacha:12,morozko:15};
  function mode(){return kind==='dacha'&&evening()?'fireflies':kind;}
  function spawn(fresh){const m=mode(),p={x:rnd(0,W),y:rnd(0,H),t:rnd(0,100),age:0};
    switch(m){
      case 'sukno':Object.assign(p,{g:pick(['♠','♥','♦','♣']),sz:rnd(16,28),a:rnd(.07,.13),vy:-rnd(6,12),rot:rnd(-.4,.4),vr:rnd(-.08,.08)});if(!fresh)p.y=H+30;break;
      case 'barhat':Object.assign(p,{r:rnd(1.4,2.8),a:rnd(.15,.35),vx:rnd(-6,6),vy:rnd(-5,3)});break;
      case 'izba':Object.assign(p,{r:rnd(1,2.1),vy:-rnd(18,34),vx:rnd(-4,4),life:rnd(4,7)});p.y=fresh?rnd(H*.3,H):H+rnd(0,20);break;
      case 'yarmarka':Object.assign(p,{w:rnd(4,6),h:rnd(7,10),c:pick(['#ffd88a','#ff9a8a','#9fd6ff','#bff0a8']),vy:rnd(10,18),rot:rnd(0,6),vr:rnd(-1.5,1.5)});if(!fresh)p.y=-12;break;
      case 'palaty':Object.assign(p,{sz:rnd(4,9),life:rnd(2.5,4.5)});p.age=fresh?rnd(0,p.life):0;break;
      case 'kupe':Object.assign(p,{r:rnd(30,60),a:rnd(.14,.24),vx:-rnd(22,45),c:pick(['255,214,150','255,236,200','200,220,255'])});p.y=rnd(H*.08,H*.7);if(!fresh)p.x=W+p.r;break;
      case 'dacha':Object.assign(p,{w:rnd(3,4.5),h:rnd(6,8),vy:rnd(11,19),rot:rnd(0,6),vr:rnd(-.8,.8),c:pick(['#ffd3de','#ffe4ea','#f9b9c9'])});if(!fresh)p.y=-12;break;
      case 'fireflies':Object.assign(p,{r:rnd(1.6,2.4),vx:rnd(-8,8),vy:rnd(-8,8)});break;
      case 'morozko':Object.assign(p,{r:rnd(1.4,3.4),a:rnd(.45,.8),vy:rnd(14,30)});if(!fresh)p.y=-8;break;}
    return p;}
  function reset(){parts=[];const n=COUNT[kind]||10;for(let i=0;i<n;i++)parts.push(spawn(true));}
  function size(){if(!cv)return;const r=cv.getBoundingClientRect();dpr=Math.min(2,window.devicePixelRatio||1);W=r.width;H=r.height;cv.width=Math.round(W*dpr);cv.height=Math.round(H*dpr);}
  function step(dt){const m=mode();
    for(let i=0;i<parts.length;i++){let p=parts[i];p.t+=dt;p.age+=dt;
      switch(m){
        case 'sukno':p.y+=p.vy*dt;p.x+=Math.sin(p.t*.5)*6*dt;p.rot+=p.vr*dt;if(p.y<-40)p=parts[i]=spawn(false);break;
        case 'barhat':case 'fireflies':p.x+=p.vx*dt+Math.sin(p.t*.7)*4*dt;p.y+=p.vy*dt+Math.cos(p.t*.6)*4*dt;
          if(p.x<-10)p.x=W+10;if(p.x>W+10)p.x=-10;if(p.y<-10)p.y=H+10;if(p.y>H+10)p.y=-10;break;
        case 'izba':p.y+=p.vy*dt;p.x+=(p.vx+Math.sin(p.t*2)*8)*dt;if(p.age>p.life||p.y<-10)p=parts[i]=spawn(false);break;
        case 'yarmarka':case 'dacha':p.y+=p.vy*dt;p.x+=Math.sin(p.t*.9)*14*dt;p.rot+=p.vr*dt;if(p.y>H+14)p=parts[i]=spawn(false);break;
        case 'palaty':if(p.age>p.life)p=parts[i]=spawn(false);break;
        case 'kupe':p.x+=p.vx*dt;if(p.x<-p.r-10)p=parts[i]=spawn(false);break;
        case 'morozko':p.y+=p.vy*dt;p.x+=Math.sin(p.t*.8+p.r)*10*dt;if(p.y>H+8)p=parts[i]=spawn(false);break;}}}
  function glow(x,y,r,rgb,a){const g=ctx.createRadialGradient(x,y,0,x,y,r);g.addColorStop(0,`rgba(${rgb},${a})`);g.addColorStop(1,`rgba(${rgb},0)`);ctx.fillStyle=g;ctx.beginPath();ctx.arc(x,y,r,0,7);ctx.fill();}
  function draw(){const m=mode();ctx.setTransform(dpr,0,0,dpr,0,0);ctx.clearRect(0,0,W,H);
    for(const p of parts){ctx.save();
      switch(m){
        case 'sukno':ctx.translate(p.x,p.y);ctx.rotate(p.rot);ctx.globalAlpha=p.a;ctx.fillStyle='#f6ead0';ctx.font=`${p.sz}px serif`;ctx.textAlign='center';ctx.fillText(p.g,0,0);break;
        case 'barhat':glow(p.x,p.y,p.r*3,'215,228,255',p.a*(.6+.4*Math.sin(p.t*1.3)));break;
        case 'izba':{const k=1-p.age/p.life;glow(p.x,p.y,p.r*3,'255,176,80',.55*k);break;}
        case 'yarmarka':case 'dacha':ctx.translate(p.x,p.y);ctx.rotate(p.rot);ctx.scale(1,Math.abs(Math.cos(p.t*1.6))*.7+.3);ctx.globalAlpha=m==='dacha'?.6:.4;ctx.fillStyle=p.c;
          if(m==='dacha'){ctx.beginPath();ctx.ellipse(0,0,p.w,p.h/2,0,0,7);ctx.fill();}else ctx.fillRect(-p.w/2,-p.h/2,p.w,p.h);break;
        case 'palaty':{const a=Math.sin(Math.PI*p.age/p.life)*.55,s=p.sz*(.6+.4*Math.sin(Math.PI*p.age/p.life));ctx.translate(p.x,p.y);ctx.globalAlpha=a;ctx.fillStyle='#ffdf96';
          ctx.beginPath();ctx.moveTo(0,-s);ctx.quadraticCurveTo(0,0,s,0);ctx.quadraticCurveTo(0,0,0,s);ctx.quadraticCurveTo(0,0,-s,0);ctx.quadraticCurveTo(0,0,0,-s);ctx.fill();break;}
        case 'kupe':glow(p.x,p.y,p.r,p.c,p.a);break;
        case 'fireflies':glow(p.x,p.y,p.r*5,'226,255,140',.45*Math.max(0,Math.sin(p.t*1.1+p.x)));break;
        case 'morozko':ctx.globalAlpha=p.a;ctx.fillStyle='#fff';ctx.beginPath();ctx.arc(p.x,p.y,p.r,0,7);ctx.fill();break;}
      ctx.restore();}}
  function frame(now){raf=0;if(!active())return;raf=requestAnimationFrame(frame);
    if(now-last<32)return;const dt=Math.min(.1,(now-last)/1000||0);last=now;step(dt);draw();}
  function active(){return want&&cv&&!document.hidden;}
  function start(){if(raf||!active())return;size();if(!parts.length)reset();last=performance.now();raf=requestAnimationFrame(frame);}
  function stop(){if(raf)cancelAnimationFrame(raf);raf=0;if(ctx)ctx.clearRect(0,0,cv.width,cv.height);}
  document.addEventListener('visibilitychange',()=>{if(document.hidden)stop();else start();});
  addEventListener('resize',()=>{if(raf){size();reset();}});
  return {
    attach(host){if(cv)return;cv=document.createElement('canvas');cv.className='fxc';cv.setAttribute('aria-hidden','true');host.appendChild(cv);ctx=cv.getContext('2d');},
    set(k){if(k===kind)return;kind=k;parts=[];if(raf){size();reset();}},
    run(on){want=!!on;if(want)start();else stop();},
    get kind(){return mode();}
  };
})();

// Characters: portrait recipe, playing style and lines. Missing lines fall back to DEFAULT_LINES.
function face(o){ // compact portrait generator, 40x40
  const skin=o.skin||'#f1cfa0',hair=o.hair||'#7a4a2a';let back='',front='',beard='';
  if(o.hairLong)back+=`<path d="M9 20c0-10 5-15 11-15s11 5 11 15v12h-4V22H13v10H9z" fill="${hair}"/>`;
  if(o.beard==='short')beard=`<path d="M12 24c1 7 4 10 8 10s7-3 8-10c-2 2-5 3-8 3s-6-1-8-3z" fill="${o.beardCol||hair}"/>`;
  if(o.beard==='long')beard=`<path d="M11 23c0 10 4 15 9 15s9-5 9-15c-2 3-5 4-9 4s-7-1-9-4z" fill="${o.beardCol||hair}"/>`;
  if(o.mous)beard+=`<path d="M15 25.5c2-1.5 3.5-1.5 5 0 1.5-1.5 3-1.5 5 0-2 .8-3.5 .8-5 0-1.5 .8-3 .8-5 0z" fill="${o.beardCol||hair}"/>`;
  const H=o.hat;
  if(H==='cap')front=`<path d="M10 14c0-6 4-9 10-9s10 3 10 9z" fill="#3c4a5c"/><path d="M8 14h20c-1 2-4 3-10 3s-9-1-10-3z" fill="#232c38"/><circle cx="25" cy="9" r="2" fill="#d94a4a"/>`;
  if(H==='jester')front=`<path d="M10 15 4 5l9 4 7-6 7 6 9-4-6 10z" fill="#d23b3b"/><path d="M20 3l7 6 9-4-6 10H20z" fill="#2f7a46"/><circle cx="4" cy="5" r="2.2" fill="#e6b450"/><circle cx="36" cy="5" r="2.2" fill="#e6b450"/><circle cx="20" cy="3" r="2.2" fill="#e6b450"/>`;
  if(H==='kerchief')back=`<path d="M6 30C6 13 12 5 20 5s14 8 14 25l-4 2c-1-8-5-11-10-11s-9 3-10 11z" fill="${o.cloth||'#2d6db5'}"/>`+back,front=`<path d="M10 15c3-5 17-5 20 0-4-2-16-2-20 0z" fill="${o.cloth||'#2d6db5'}"/><g fill="#fff" opacity=".8"><circle cx="12" cy="11" r="1"/><circle cx="20" cy="7" r="1"/><circle cx="28" cy="11" r="1"/></g>`;
  if(H==='shako')front=`<path d="M11 15V5h18v10z" fill="#1f2a44"/><rect x="11" y="12" width="18" height="3" fill="#c23a3a"/><path d="M9 15h22l-2 3H11z" fill="#111827"/><circle cx="20" cy="8" r="2.4" fill="#e6b450"/>`;
  if(H==='bonnet')front=`<path d="M8 16c0-8 5-12 12-12s12 4 12 12z" fill="#7b3f8c"/><path d="M5 16h30c-2 2-8 3-15 3S7 18 5 16z" fill="#5b2c68"/><path d="M27 6c5-5 9-2 8 2-3-1-5 0-7 2z" fill="#f3d36b"/>`;
  if(H==='gorlatka')front=`<path d="M11 15 13 0h14l2 15z" fill="#4a2e22"/><rect x="9" y="13" width="22" height="5" rx="2.5" fill="#8b6a4a"/>`;
  if(H==='helmet')front=`<path d="M10 16c0-8 4-13 10-13s10 5 10 13z" fill="#9aa4b2"/><path d="M20 0l2 4h-4z" fill="#9aa4b2"/><rect x="9" y="14" width="22" height="3" fill="#6b7480"/><rect x="19" y="14" width="2" height="9" fill="#6b7480"/>`;
  if(H==='kokoshnik')front=`<path d="M8 17C8 6 13 1 20 1s12 5 12 16z" fill="#c2272d"/><path d="M11 16C12 8 15 4 20 4s8 4 9 12" fill="none" stroke="#e6b450" stroke-width="1.6"/><g fill="#fff3d6"><circle cx="20" cy="8" r="1.8"/><circle cx="14" cy="11" r="1.2"/><circle cx="26" cy="11" r="1.2"/></g>`;
  if(H==='crown')front=`<rect x="9" y="11" width="22" height="6" rx="3" fill="#f2efe8"/><g fill="#1d1d26"><circle cx="13" cy="14" r=".8"/><circle cx="20" cy="14" r=".8"/><circle cx="27" cy="14" r=".8"/></g><path d="M11 11 12 1l4 5 4-6 4 6 4-5 1 10z" fill="#e6b450" stroke="#8a5d16" stroke-width=".8"/><circle cx="20" cy="4" r="1.6" fill="#c2272d"/>`;
  if(H==='bald')front=`<path d="M11 18c0-4 1-6 2-7M29 18c0-4-1-6-2-7" stroke="${hair}" stroke-width="3" fill="none"/>`;
  if(!H||H==='hair')front=`<path d="M11 16c0-7 4-11 9-11s9 4 9 11c-3-3-6-4-9-4s-6 1-9 4z" fill="${hair}"/>`;
  if(H==='leaves')front=`<g fill="${o.cloth||'#3f7a3a'}"><path d="M8 16c-2-6 2-11 6-11-1 3 0 5 2 6-3 0-6 2-8 5z"/><path d="M32 16c2-6-2-11-6-11 1 3 0 5-2 6 3 0 6 2 8 5z"/><path d="M14 9c1-5 4-8 6-8s5 3 6 8c-2-2-4-3-6-3s-4 1-6 3z"/></g>`;
  if(H==='cat')front=`<path d="M9 14 8 2l8 7zM31 14l1-12-8 7z" fill="${o.skin||'#8d8f98'}" stroke="#5c5e66" stroke-width=".8"/><path d="M10 12 9.5 5l4 4zM30 12l.5-7-4 4z" fill="#e8a5a5"/>`;
  if(H==='hood')back=`<path d="M6 34C6 14 12 4 20 4s14 10 14 30l-5 2c0-9-4-14-9-14s-9 5-9 14z" fill="${o.cloth||'#3b3b44'}"/>`+back,front=`<path d="M9 17C10 9 14 5 20 5s10 4 11 12c-3-3-7-5-11-5s-8 2-11 5z" fill="${o.cloth||'#3b3b44'}"/>`;
  if(H==='spikes')front=`<g fill="${o.cloth||'#2f6b3c'}"><path d="M10 15 8 4l6 6zM20 12 20 0l4 9zM30 15l2-11-6 6z"/></g>`;
  let acc='';
  if(o.glasses)acc+=`<g fill="none" stroke="#2b2b33" stroke-width="1"><circle cx="16" cy="20" r="2.6"/><circle cx="24" cy="20" r="2.6"/><path d="M18.6 20h2.8"/></g>`;
  if(o.quill)acc+=`<path d="M30 6c4 2 6 8 3 12l-4-9z" fill="#f4f1e8" stroke="#9a8f7a" stroke-width=".6"/>`;
  if(o.keys)acc+=`<g stroke="#b88a2e" stroke-width="1.4" fill="none"><circle cx="31" cy="33" r="2.2"/><path d="M31 35v4M31 37h2"/></g>`;
  if(o.whiskers)acc+=`<g stroke="#2b2b33" stroke-width=".7"><path d="M10 24h6M10 26.5l6-1M30 24h-6M30 26.5l-6-1"/></g><path d="M19 22.5h2l-1 1.5z" fill="#d0697a"/>`;
  if(o.nose)acc+=`<path d="M20 19c3 3 4 6 1 8-1 .6-3 .3-3-1" fill="${o.skin||'#e2b98f'}" stroke="#8a5a3a" stroke-width=".8"/>`;
  if(o.gaunt)acc+=`<path d="M13 23c1 3 2 4 3 4M27 23c-1 3-2 4-3 4" stroke="#6b6f7a" stroke-width=".9" fill="none"/>`;
  if(o.eyesRed)acc+=`<circle cx="16.5" cy="20" r="1.4" fill="#d23b3b"/><circle cx="23.5" cy="20" r="1.4" fill="#d23b3b"/>`;
  if(o.blush)acc+=`<circle cx="14" cy="24" r="2" fill="#e8908a" opacity=".55"/><circle cx="26" cy="24" r="2" fill="#e8908a" opacity=".55"/>`;
  const brow=o.stern?`<path d="M13.5 16.5l4 1M26.5 16.5l-4 1" stroke="#2b1d16" stroke-width="1.2" stroke-linecap="round"/>`:'';
  const mouth=o.sad?`<path d="M17 27c2-1.5 4-1.5 6 0" stroke="#7a3b2e" stroke-width="1.2" fill="none" stroke-linecap="round"/>`:`<path d="M16.5 26c2 1.8 5 1.8 7 0" stroke="#7a3b2e" stroke-width="1.2" fill="none" stroke-linecap="round"/>`;
  return `<svg viewBox="0 0 40 40" aria-hidden="true">${back}<ellipse cx="20" cy="21" rx="9" ry="10" fill="${skin}"/><circle cx="16.5" cy="20" r="1.3" fill="#2b1d16"/><circle cx="23.5" cy="20" r="1.3" fill="#2b1d16"/>${brow}${mouth}${beard}${front}${acc}</svg>`;
}
const DEFAULT_LINES={start:['Сыграем.'],lead:['Ходи.','Держи.'],toss:['Подкину.','И эту.'],take:['Беру.'],beat:['Покрыто.'],bito:['Бито.'],
  transfer:['Перевожу.'],playerTook:['Бери, бери.'],win:['Ну вот и всё.'],lose:['Твоя взяла.'],draw:['Ничья.'],out:['Я вышел!']};
const CHARS={
  vanka:{short:'Ванька',name:'Ванька-пастух',style:'easy',over:{noise:.35},lvl:1,blurb:'Молодой и горячий: ходит с чего попало, а потом чешет затылок.',
    pic:face({hair:'#c58b3c',hat:'cap',blush:1}),
    lines:{start:['Ну чё, сыграем?','Коровы подождут!'],lead:['На!','А вот так!'],take:['Эх, ладно…','Беру, чего уж.'],beat:['Ха, отбил!'],win:['Вот это я понимаю!'],lose:['Да ну тебя…'],out:['Я всё!']}},
  kuzmich:{short:'Кузьмич',name:'Кузьмич',style:'easy',lvl:1,blurb:'Осторожный дед. Сомневается — берёт, козыри бережёт до последнего.',pic:PORTRAITS.kuzmich,
    lines:{start:['Ну, поехали, внучок.','Сыграем, пока чай стынет.'],lead:['Держи.','А вот так.','Ну-ка, отбейся.'],toss:['Подкину-ка.','И эту.'],
      take:['Ладно, беру.','Эх, придётся взять.'],beat:['Крою.','Так-то!'],bito:['Бито, твоя взяла.','Отпускаю.'],transfer:['Переведу-ка.'],
      playerTook:['Бери, не стесняйся.'],win:['Хе-хе, дурачок!','Опыт не пропьёшь.'],lose:['Ну ты даёшь!','Обыграл старика.'],out:['Я своё отыграл.']}},
  nura:{short:'Нюра',name:'Баба Нюра',style:'sly',lvl:2,blurb:'Подкидывает всё, что можно, и обожает переводить. Не зевай.',pic:PORTRAITS.nura,
    lines:{start:['Садись, милок, сыграем.','Ну, держись!'],lead:['А вот тебе!','Получай!'],toss:['И это возьми!','А ещё вот!'],
      take:['Ой, беру, беру.','Ладно уж, давай сюда.'],beat:['Не на ту напал!'],bito:['Бито, бито.'],transfer:['Сам отбивайся!','Переводик тебе!'],
      playerTook:['Бери, бери, не жалко!'],win:['Учись, пока я жива!'],lose:['Ох, обыграл старуху!'],out:['А я уже всё, милки!']}},
  tishka:{short:'Тишка',name:'Скоморох Тишка',style:'sly',over:{transferBias:1,multi:.9},lvl:2,blurb:'Шут ярмарочный: переводит при каждой возможности и дразнится.',
    pic:face({hair:'#d9a441',hat:'jester',blush:1}),
    lines:{start:['Эй, честной народ!','Карты в руки — смех в штаны!'],transfer:['Опа — тебе!','Лови, не урони!','Скок-перескок!'],take:['Ой-ой, беру-беру!'],
      beat:['Ха! Мимо!'],win:['Дурака валять — моё ремесло!'],lose:['Ну и шутка вышла…'],out:['Я — прыг, и нету!']}},
  matryona:{short:'Матрёна',name:'Торговка Матрёна',style:'bold',lvl:2,blurb:'Шумная и щедрая: подкидывает охапками, лишь бы ты взял.',
    pic:face({hat:'kerchief',cloth:'#d0712c',blush:1}),
    lines:{start:['Подходи, не стесняйся!'],toss:['И это в придачу!','Бери оптом!'],take:['Ладно, заверните.'],playerTook:['Носи на здоровье!'],win:['Торг уместен — и я победила!'],lose:['Ох, проторговалась.'],out:['Распродалась!']}},
  kupets:{short:'Савва',name:'Купец Савва',style:'shrewd',lvl:3,blurb:'Считает каждую карту, бережёт козыри и не прощает ошибок в концовке.',pic:PORTRAITS.kupets,
    lines:{start:['Начнём торг.','Посмотрим, чего вы стоите.'],lead:['Извольте.','Прошу.'],toss:['Добавлю товару.'],take:['Беру. Временно.','Убыток, но беру.'],
      beat:['Покрыто.','Невыгодно вам.'],bito:['Бито. Сделка закрыта.'],transfer:['Передаю по накладной.'],playerTook:['Записываю на ваш счёт.'],
      win:['Чистая прибыль!','Я же всё посчитал.'],lose:['Ловко торгуете!'],out:['Сделка закрыта.']}},
  prokhor:{short:'Прохор',name:'Солдат Прохор',style:'bold',over:{noise:.06},lvl:2,blurb:'Бравый служивый: давит напором и не боится брать.',
    pic:face({hat:'shako',mous:1,hair:'#4a3020',stern:1}),
    lines:{start:['Смирно! Сдаю.'],lead:['В атаку!','Ура!'],toss:['Подкрепление!'],take:['Отступаю на позиции.'],beat:['Отбито!'],win:['Победа за нами!'],lose:['Ретируюсь…'],out:['Задание выполнено!']}},
  akim:{short:'Аким',name:'Писарь Аким',style:'shrewd',over:{multi:.3},lvl:3,blurb:'Всё записывает: какие карты вышли, у кого что осталось.',
    pic:face({hair:'#8a7a6a',hat:'hair',glasses:1,quill:1}),
    lines:{start:['Записываю: партия первая.'],lead:['Пункт первый.'],take:['Внесём в опись.'],beat:['Согласно описи — бито.'],win:['Так и запишем: дурак.'],lose:['Ошибочка в расчётах…'],out:['Подпись, печать — я вышел.']}},
  aglaya:{short:'Аглая',name:'Барыня Аглая',style:'sly',over:{greed:1.2},lvl:2,blurb:'Капризная барыня: брать не любит, переводит с удовольствием.',
    pic:face({hat:'bonnet',blush:1,hairLong:1,hair:'#3b2a1f'}),
    lines:{start:['Ах, какая скука. Сыграем.'],transfer:['Это вам, голубчик.'],take:['Фу, как неприятно.'],win:['Мерси за партию!'],lose:['Ах, какая досада!'],out:['Я удаляюсь.']}},
  voevoda:{short:'Ратибор',name:'Воевода Ратибор',style:'bold',over:{noise:.03,greed:.8},lvl:3,blurb:'Стратег: бьёт крупно и держит козыри для решающего удара.',
    pic:face({hat:'helmet',beard:'short',hair:'#5a3a24',stern:1}),
    lines:{start:['К бою!'],lead:['Вперёд, дружина!'],take:['Отходим.'],beat:['Щит держит!'],win:['Поле за мной!'],lose:['Достойный противник.'],out:['Я своё отвоевал.']}},
  klyuchnitsa:{short:'Марфа',name:'Ключница Марфа',style:'shrewd',over:{multi:.7},lvl:3,blurb:'Хозяйка терема: каждую карту помнит, как каждый ключ.',
    pic:face({hat:'kerchief',cloth:'#5b3a7a',keys:1,stern:1}),
    lines:{start:['Всё у меня под замком.'],take:['Приберу.'],beat:['Заперто!'],win:['Порядок в доме!'],lose:['Недосмотрела…'],out:['Ключи сданы.']}},
  boyarin:{short:'Ферапонт',name:'Боярин Ферапонт',style:'master',over:{transferBias:.5},lvl:4,blurb:'Важный и неторопливый, но играет так, будто видит твои карты.',
    pic:face({hat:'gorlatka',beard:'long',hair:'#3a2a1c',stern:1}),
    lines:{start:['Ну-с, извольте.'],lead:['По чину.'],take:['Беру. По-боярски.'],beat:['Не по чину вам.'],win:['Знай своё место!'],lose:['Неслыханно!'],out:['Боярин удаляется.']}},
  nesmeyana:{short:'Несмеяна',name:'Царевна Несмеяна',style:'master',over:{multi:.4,transferBias:.9},lvl:4,blurb:'Ни разу не улыбнулась. Может, хоть твоя игра её рассмешит?',
    pic:face({hat:'kokoshnik',hairLong:1,hair:'#7a4a2a',sad:1}),
    lines:{start:['…','Сыграем. Мне всё равно.'],lead:['Ходи.'],take:['Скучно. Беру.'],beat:['Предсказуемо.'],win:['Даже не смешно.'],lose:['Хм. Это было… забавно.'],out:['Я пойду.']}},
  // ---- Постоялый двор
  erofey:{short:'Ерофей',name:'Ямщик Ерофей',style:'bold',over:{noise:.1},lvl:2,blurb:'Гонит, как тройку по тракту: ходит быстро и смело.',
    pic:face({hat:'cap',beard:'short',hair:'#5a3a24'}),
    lines:{start:['Эх, прокачу!','По коням!'],lead:['Н-но, пошла!'],take:['Тпру… беру.'],beat:['Объехал!'],win:['Довёз с ветерком!'],lose:['Застрял в колее…'],out:['Приехали!']}},
  pelageya:{short:'Пелагея',name:'Трактирщица Пелагея',style:'sly',lvl:2,blurb:'Хозяйка постоялого двора: подливает чаю и подкидывает карт.',
    pic:face({hat:'kerchief',cloth:'#b8322c',blush:1}),
    lines:{start:['Чайку? А потом в картишки.'],toss:['Вот ещё к чаю!'],take:['Запишу на свой счёт.'],win:['Заходите ещё!'],lose:['Ну, за счёт заведения.'],out:['Пойду самовар ставить.']}},
  foma:{short:'Фома',name:'Странник Фома',style:'shrewd',over:{mc:{ms:30,horizon:2}},lvl:3,blurb:'Исходил полсвета и повидал всякие игры. Смотрит в оба.',
    pic:face({hat:'hood',cloth:'#6b5a46',beard:'long',hair:'#8a8378'}),
    lines:{start:['Мир дому сему.'],lead:['С Богом.'],take:['Ноша не тянет.'],beat:['Всё в свой черёд.'],win:['Дорога всё рассудит.'],lose:['Смиряюсь.'],out:['Пойду дальше.']}},
  // ---- Избушка Бабы-Яги
  bayun:{short:'Баюн',name:'Кот Баюн',style:'sly',over:{transferBias:1},lvl:3,blurb:'Мурлычет сказки и усыпляет бдительность. Переводит хитро.',
    pic:face({hat:'cat',skin:'#8d8f98',whiskers:1}),
    lines:{start:['Мур-р… сыграем?'],lead:['Мяу.'],transfer:['Мур-р, тебе!'],take:['Фыр-р.'],beat:['Цап!'],win:['Сладко спи, дурачок…'],lose:['Ш-ш-ш!'],out:['Мур-р-р, я на печку.']}},
  leshy:{short:'Леший',name:'Леший',style:'bold',over:{noise:.05,greed:.75},lvl:3,blurb:'Хозяин леса. Водит кругами и подкидывает охапками.',
    pic:face({hat:'leaves',skin:'#b7c48a',beard:'long',beardCol:'#6b7a3a',stern:1}),
    lines:{start:['Заблудился, путник?'],toss:['Ещё веточку!'],take:['Ух-ху-ху…'],beat:['Не пройдёшь!'],win:['Кружи теперь по лесу!'],lose:['Вывел-таки…'],out:['Ушёл в чащу.']}},
  yaga:{short:'Яга',name:'Баба-Яга',style:'master',over:{mc:{ms:80,horizon:3}},lvl:4,blurb:'Колдует над колодой: козырь у неё под платком. Хитра и злопамятна.',
    pic:face({hat:'kerchief',cloth:'#3b3b44',nose:1,skin:'#d9c7a3',stern:1}),
    lines:{start:['Фу-фу, русским духом пахнет!','Садись, касатик…'],lead:['Ступа, вперёд!'],toss:['И это в котёл!'],take:['Ишь ты…'],beat:['Не на ту напал!'],transfer:['Иди-ка ты сам!'],
      win:['В печь его!'],lose:['Ох, пропала моя головушка…'],out:['Улетаю на ступе!']}},
  // ---- Богатырская застава
  alesha:{short:'Алёша',name:'Алёша Попович',style:'sly',over:{multi:.9},lvl:3,blurb:'Самый младший и самый хитрый из богатырей.',
    pic:face({hat:'helmet',hair:'#c58b3c',blush:1}),
    lines:{start:['Ну, братцы, потешимся!'],toss:['Хитростью возьму!'],take:['Отступлю для виду.'],win:['Смекалка — сила!'],lose:['Перехитрили!'],out:['Я — на коня!']}},
  dobrynya:{short:'Добрыня',name:'Добрыня Никитич',style:'shrewd',lvl:3,blurb:'Рассудительный богатырь: без нужды не рискует.',
    pic:face({hat:'helmet',beard:'short',hair:'#7a4a2a'}),
    lines:{start:['Сыграем по-честному.'],lead:['Иду.'],take:['Приму.'],beat:['Отражено.'],win:['Правда за нами.'],lose:['Достойно.'],out:['Застава моя ждёт.']}},
  ilya:{short:'Илья',name:'Илья Муромец',style:'master',over:{greed:.85},lvl:4,blurb:'Старший богатырь. Медленно запрягает, да быстро едет.',
    pic:face({hat:'helmet',beard:'long',hair:'#3a2a1c',beardCol:'#4a3524',stern:1}),
    lines:{start:['Тридцать лет сидел — теперь сыграю.'],lead:['Раззудись, плечо!'],take:['Сдюжим.'],beat:['Как щитом!'],win:['Вот и вся сказка.'],lose:['Силён ты, удалец!'],out:['Пойду на заставу.']}},
  // ---- Купеческий дом
  mitrofan:{short:'Митрофан',name:'Приказчик Митрофан',style:'sly',lvl:2,blurb:'Шустрый приказчик: подкидывает, как товар на прилавок.',
    pic:face({hair:'#4a3020',mous:1}),
    lines:{start:['Чего изволите?'],toss:['Вот, свеженькое!'],take:['Беру на склад.'],win:['Обслужил!'],lose:['Хозяин заругает…'],out:['Лавка закрыта!']}},
  varvara:{short:'Варвара',name:'Купчиха Варвара',style:'shrewd',over:{multi:.6},lvl:3,blurb:'Хозяйка дома. Сундуки полны, а в картах — расчёт.',
    pic:face({hat:'kokoshnik',hairLong:1,hair:'#5a3a24',blush:1}),
    lines:{start:['Милости просим к столу.'],lead:['Извольте.'],take:['Приму в счёт.'],beat:['Не продешевлю.'],win:['Барыш мой!'],lose:['Убыток, ох убыток…'],out:['Пойду считать прибыль.']}},
  // ---- Кощеево царство
  kikimora:{short:'Кикимора',name:'Кикимора болотная',style:'sly',over:{transferBias:1,multi:.8},lvl:3,blurb:'Шуршит, путает, переводит при всякой возможности.',
    pic:face({hairLong:1,hair:'#4f6a3a',skin:'#a9b98f',hat:'hair'}),
    lines:{start:['Хи-хи… сыграем?'],transfer:['Тебе, тебе!'],take:['Ой, утопила…'],win:['В болото его!'],lose:['Ш-ш-ш…'],out:['Ушла в трясину.']}},
  gorynych:{short:'Горыныч',name:'Змей Горыныч',style:'bold',over:{greed:.65,tossMax:6},lvl:4,blurb:'Три головы — три мнения, но подкидывают все разом.',
    pic:face({hat:'spikes',cloth:'#2f6b3c',skin:'#7fb069',eyesRed:1,stern:1}),
    lines:{start:['Р-р-р! Сыграем!'],toss:['Пламя!','Ещё огня!'],take:['Р-р…'],beat:['Сгорело!'],win:['Испепелю!'],lose:['Головы кругом…'],out:['Улетаю!']}},
  koschei:{short:'Кощей',name:'Кощей Бессмертный',style:'master',over:{mc:{ms:130,horizon:3},searchBudget:40000,cheat:true},lvl:5,blurb:'Смерть его в игле, а игла — в колоде. Играет без жалости.',
    pic:face({hat:'crown',skin:'#c9cdd6',gaunt:1,eyesRed:1,hair:'#3a3a40',stern:1}),
    lines:{start:['Ха-ха-ха! Ещё один дурак…'],lead:['Трепещи!'],toss:['Не уйдёшь!'],take:['Бессмертному не страшно.'],beat:['Тщетно!'],transfer:['Сам отбивайся, смертный!'],
      win:['Бессмертие за мной!'],lose:['Нашли… иглу…'],out:['Я вечен!']}},
  tsar:{short:'Царь',name:'Царь Горох',style:'master',over:{searchBudget:40000},lvl:5,blurb:'Сам царь-батюшка. Обыграешь — получишь полцарства.',
    pic:face({hat:'crown',beard:'long',beardCol:'#e8e1d6',hair:'#e8e1d6',mous:1}),
    lines:{start:['Ну, удалец, садись.','Полцарства на кону!'],lead:['Царский ход!'],toss:['Добавлю.'],take:['Царь тоже берёт.'],beat:['Не по зубам!'],
      transfer:['Повелеваю — отбивайся!'],win:['Ступай, дурень, к своим коровам.'],lose:['Быть по сему: полцарства твои!'],out:['Царь выходит из-за стола.']}}
};
function charLine(id,k){if(!CHARS[id])return '';const L=(CHARS[id].lines[k]||DEFAULT_LINES[k]||[]);return L[Math.floor(Math.random()*L.length)]||'';}
function charPersona(id){const c=CHARS[id];return Object.assign({},STYLES[c.style],c.over||{});}

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

/* ---------- save ---------- */
const DEF_SET={hl:true,sort:'suit',trumpEnd:true,speed:'normal',snd:true,mus:1,
  fx:(window.matchMedia&&matchMedia('(prefers-reduced-motion: reduce)').matches)?0:1};
function freshSave(){return {v:2,coins:0,set:Object.assign({},DEF_SET),owned:['gzhel','sukno','classic'],back:'gzhel',face:'classic',tableSkin:'sukno',
  camp:{},daily:{day:'',done:false},quick:{deck:36,jokers:false,rules:{},players:2,mode:'podkidnoy',level:'medium'},gift:{day:'',streak:0},ach:{},
  st:{games:0,wins:0,losses:0,draws:0,streak:0,bestStreak:0,pogGiven:0,pogGot:0,noTakeWins:0,transfers:0,takes:0,firstOuts:0,bigWins:0,sixWins:0,win54:0,dailyCount:0,coinsEarned:0,
      byMode:{podkidnoy:{g:0,w:0},perevodnoy:{g:0,w:0}},byDeck:{36:{g:0,w:0},54:{g:0,w:0}},byPlayers:{}}};}
let save=freshSave();
try{const s=JSON.parse(localStorage.getItem('durak_v2')||'null');if(s&&s.v===2){const f=freshSave();save=Object.assign(f,s);save.set=Object.assign({},DEF_SET,s.set||{});save.st=Object.assign(f.st,s.st||{});save.quick=Object.assign(f.quick,s.quick||{});if(!save.owned.includes('classic'))save.owned.push('classic');if(!save.face)save.face='classic';}}catch(e){}
const persist=()=>{try{localStorage.setItem('durak_v2',JSON.stringify(save));}catch(e){}if(window.__cloud)try{window.__cloud(save);}catch(e){}};
const stageKey=(l,i)=>l+'.'+i;
const stageRec=(l,i)=>save.camp[stageKey(l,i)]||{won:false,stars:[0,0,0]};
function starsTotal(){let n=0;for(const k in save.camp)n+=save.camp[k].stars.reduce((a,b)=>a+b,0);return n;}
function locDone(li){return stageRec(LOCS[li].id,LOCS[li].stages.length-1).won;}
function locsDone(){let n=0;LOCS.forEach((l,i)=>{if(locDone(i))n++;});return n;}
function locOpen(li){return li===0||locDone(li-1);}
function stageOpen(li,si){return locOpen(li)&&(si===0||stageRec(LOCS[li].id,si-1).won);}
function achStats(){return Object.assign({},save.st,{stars:starsTotal(),locsDone:locsDone(),owned:save.owned.length});}
function newAch(){const s=achStats();return ACH.filter(a=>!save.ach[a.id]&&a.f(s));}
function dayKey(){const d=new Date();return d.getFullYear()+'-'+(d.getMonth()+1)+'-'+d.getDate();}

/* ---------- daily challenge: same task for everyone on a given day ---------- */
const DAILY_REWARD=80;
function dailyTask(){const d=dayKey();let h=7;for(const ch of d)h=(h*31+ch.charCodeAt(0))>>>0;
  // a task swapped for another (after an ad) stays swapped for the rest of the day
  if(save.dailyAlt&&save.dailyAlt.day===d)h=(h^(save.dailyAlt.n*2654435761))>>>0;const r=makeRng(h);
  const mode=r()<.5?'podkidnoy':'perevodnoy',deck=r()<.3?54:36,players=2+Math.floor(r()*3),big=deck===54;
  // goal numbers fitted by simulation so a good player manages them in roughly a third of the wins or more
  const pool=['take'+(players===2?(big?5:1):players===3?(big?1:0):(big?1:0))];
  if(mode==='perevodnoy')pool.push('transfer'+(players===4?1:2));
  if(players>2)pool.push('first');else pool.push('fast'+(big?34:14));
  const goal=pool[Math.floor(r()*pool.length)];return {mode,deck,players,goal};}
function dailyDone(){return save.daily&&save.daily.day===dayKey()&&save.daily.done;}

// Friends' table, client side: a copy of the game that follows the server.
// Cards the player may not see are stand-ins ("?"); when the server reveals one (a card played,
// a card drawn by me) the stand-in object itself becomes that card, so every reference to it
// (hand, deck, animation lists) stays valid. Seats are turned so that "me" is always seat 0.
const NET_RANKS={24:R24,36:R36,52:R52,54:R52};
function parseCardId(id){return id==='Jb'||id==='Jr'?{r:'J',s:id[1],id}:{r:id.slice(0,-1),s:id.slice(-1),id};}
let netPh=0;
function Mirror(snap,me,hooks){
  this.me=me;this.n=snap.n;this.hooks=hooks||{};this.byId={};this.bad=false;
  const n=snap.n,R=p=>(p-me+n)%n;this.R=R;this.S=p=>(p+me)%n;
  const g=Object.create(Game.prototype);this.g=g;
  g.mode=snap.mode;g.deckSize=snap.deck;g.n=n;g.rng=Math.random;g.ranks=NET_RANKS[snap.deck];g.events=[];
  const RR=snap.rules||{};g.rules={neighbors:!!RR.neighbors,show:!!RR.show,noLimit:!!RR.noLimit,cheat:!!RR.cheat};
  g.teams=snap.teams?[...Array(n)].map((_,q)=>snap.teams[this.S(q)]):null;
  const mk=id=>id?this.real(id):this.ph();
  // the trump card lies under the deck while there is one, otherwise it is somewhere in play
  g.hands=[...Array(n)].map((_,q)=>snap.hands[this.S(q)].map(mk));
  g.table=snap.table.map((x,i)=>{const pr={a:mk(x.a),d:x.d?mk(x.d):undefined};const ch=snap.cheat&&snap.cheat[i];if(ch!=null&&ch>=0)pr.cheat=R(ch);return pr;});
  g.discard=snap.discard.map(mk);
  g.trumpCard=this.byId[snap.trumpCard]||this.real(snap.trumpCard);g.trump=g.trumpCard.s;
  g.deck=[];for(let i=0;i<snap.deckLeft;i++)g.deck.push(i===0?g.trumpCard:this.ph());
  this.chest=snap.chest>=0&&snap.chest<g.deck.length?g.deck[snap.chest]:null;
  g.known=[...Array(n)].map((_,q)=>new Set(g.hands[q].filter(c=>!c.ph).map(c=>c.id)));
  g.played=[...Array(n)].map(()=>[]);g.lastPlayed=g.played.map(x=>x.slice());
  g.out=snap.out.map(R);g.att=R(snap.att);g.def=R(snap.def);g.taking=!!snap.taking;g.passed=new Set(snap.passed.map(R));g.shown=new Set(snap.shown);
  g.firstBout=snap.firstBout;g.bouts=snap.bouts;g.limit=snap.limit;g.over=snap.over;g.fool=snap.fool>=0?R(snap.fool):-1;g.pogony=snap.pogony;g.loserTeam=snap.loserTeam;
  g._ap=[];g.settle=mirrorSettle;
  this.logLen=snap.logLen;
}
const MP=Mirror.prototype;
MP.ph=function(){return {r:'?',s:'?',id:'x'+(++netPh),ph:true};};
MP.real=function(id){if(this.byId[id])return this.byId[id];const c=parseCardId(id);this.byId[id]=c;return c;};
// a stand-in becomes the real card
MP.reveal=function(obj,id){if(!obj){this.bad=true;return null;}if(obj.id===id)return obj;
  if(!obj.ph||this.byId[id]){this.bad=true;return obj;}
  const old=obj.id,c=parseCardId(id);obj.r=c.r;obj.s=c.s;obj.id=id;delete obj.ph;this.byId[id]=obj;
  if(this.hooks.reveal)this.hooks.reveal(old,obj);return obj;};
MP.cardFrom=function(p,id){const g=this.g;let c=g.hands[p].find(x=>x.id===id);if(c)return c;
  const ph=g.hands[p].find(x=>x.ph);if(!ph){this.bad=true;return null;}return this.reveal(ph,id);};
// apply one server log entry; false means the copy fell out of step and needs a fresh snapshot
MP.apply=function(e){const g=this.g,R=this.R,p=R(e.p);if(this.bad)return false;
  if(Array.isArray(e.dr))e.dr.forEach((id,j)=>{if(id)this.reveal(g.deck[g.deck.length-1-j],id);});
  const c=e.c!=null?this.cardFrom(p,e.c):null;if(this.bad)return false;
  g._ap=(e.ap||[]).map(R);let ok=false;
  switch(e.t){
    case'attack':ok=g.attack(p,c);break;case'defend':ok=g.defend(p,c,e.i);break;case'transfer':ok=g.transfer(p,c);break;
    case'show':ok=g.show(p,c);break;case'take':ok=g.take(p);break;case'done':ok=g.done(p);break;
    case'cd':ok=g.cheatDefend(p,c,e.i);break;case'ca':ok=g.cheatAttack(p,c);break;case'acc':ok=g.accuse(p);break;}
  g._ap=[];
  if(!ok){this.bad=true;return false;}
  this.finish(e);this.logLen++;return !this.bad;};
// my own move, played on the copy at once (before the server confirms it), so the card goes down without waiting.
// Who else passes is unknown here, so the copy never closes a round by itself on a guess; the confirmation fills that in.
MP.local=function(m){const g=this.g,e0=g.events.length;g._ap=[];let ok=false;const c=m.c;
  switch(m.t){case'attack':ok=g.attack(0,c);break;case'defend':ok=g.defend(0,c,m.i);break;case'transfer':ok=g.transfer(0,c);break;
    case'show':ok=g.show(0,c);break;case'take':ok=g.take(0);break;case'done':ok=g.done(0);break;
    case'cd':ok=g.cheatDefend(0,c,m.i);break;case'ca':ok=g.cheatAttack(0,c);break;}
  if(!ok)return null;
  return {t:m.t,c:c?c.id:undefined,draws:g.events.slice(e0).filter(x=>x.t==='draw').map(x=>x.c)};};
// the server's copy of a move already played here: add what only the server knew (automatic passes, cards drawn)
MP.echo=function(e,pend){const g=this.g,R=this.R;
  if(pend.draws.length){if(Array.isArray(e.dr))e.dr.forEach((id,j)=>{if(id&&pend.draws[j])this.reveal(pend.draws[j],id);});}
  else{if(Array.isArray(e.dr))e.dr.forEach((id,j)=>{if(id)this.reveal(g.deck[g.deck.length-1-j],id);});
    g._ap=(e.ap||[]).map(R);if(g._ap.length)g.settle();g._ap=[];}
  this.finish(e);this.logLen++;return !this.bad;};
MP.finish=function(e){const g=this.g,R=this.R;
  if(e.hs)e.hs.forEach((ids,sp)=>{const q=R(sp);const h=g.hands[q];ids.forEach(id=>{if(!h.some(x=>x.id===id)){const ph=h.find(x=>x.ph);if(ph)this.reveal(ph,id);}});});
  if(e.fo){g.fool=e.fo[0]>=0?R(e.fo[0]):-1;g.pogony=e.fo[1];g.loserTeam=e.fo[2];}};
// what the server will accept from me (seat 0 here) as a log move
MP.wire=function(m){const o={t:m.t};if(m.c)o.c=m.c.id;if(m.i!=null)o.i=m.i;return o;};
// settle() without peeking into hidden hands: the server says who was passed over
function mirrorSettle(){
  if(this.over||!this.table.length)return;
  if(!this.taking&&this.undefended().length>0)return;
  if(!this.taking&&this.hands[this.def].length===0)return this.endBout(false);
  for(const q of this.throwers()){if(this.passed.has(q))continue;if(this._ap.indexOf(q)>=0){this.passed.add(q);continue;}return;}
  this.endBout(this.taking);}
if(typeof module!=='undefined')module.exports={Mirror,parseCardId};

// Screens, table rendering from engine state, human input, opponents' turns, results and rewards.
const $=id=>document.getElementById(id);
const pick=a=>a[Math.floor(Math.random()*a.length)];
const MODE_NAME={podkidnoy:'Подкидной',perevodnoy:'Переводной'};
const SPEED={fast:.7,normal:1,slow:1.35};
const SP=()=>SPEED[save.set.speed]||1;
const wait=(ms,fn)=>setTimeout(fn,ms*SP());
function applySpeed(){document.documentElement.style.setProperty('--spd',(.5*SP()).toFixed(2)+'s');}
const plural=(n,a,b,c)=>{const m=n%10,h=n%100;return n+' '+(m===1&&h!==11?a:m>=2&&m<=4&&(h<12||h>14)?b:c);};

/* ---------- sound ---------- */
let ac=null;
function audio(){try{ac=ac||new (window.AudioContext||window.webkitAudioContext)();if(ac.state!=='running'&&ac.state!=='closed')ac.resume();}catch(e){}return ac;}
function noise(dur,shape,filt,freq,vol){if(!save.set.snd||!audio())return;try{const n=Math.floor(ac.sampleRate*dur),b=ac.createBuffer(1,n,ac.sampleRate),d=b.getChannelData(0);
  for(let i=0;i<n;i++)d[i]=(Math.random()*2-1)*Math.pow(1-i/n,shape);const s=ac.createBufferSource(),f=ac.createBiquadFilter(),g=ac.createGain();
  f.type=filt;f.frequency.value=freq;g.gain.value=vol;s.buffer=b;s.connect(f);f.connect(g);g.connect(ac.destination);s.start();}catch(e){}}
const flick=v=>noise(.07,3,'bandpass',2300+Math.random()*900,v||.25);
const slap=()=>noise(.12,6,'lowpass',900,.8);
const swish=()=>noise(.22,1.6,'bandpass',1500,.12);
// riffle of a deck being shuffled: a quick run of soft card flicks
const shuffleSnd=()=>{for(let i=0;i<14;i++)setTimeout(()=>flick(.12+Math.random()*.08),i*38+Math.random()*12);};
function tones(list,type,vol){if(!save.set.snd||!audio())return;try{const t=ac.currentTime;list.forEach(([f,at,len])=>{const o=ac.createOscillator(),g=ac.createGain();
  o.type=type||'triangle';o.frequency.value=f;g.gain.setValueAtTime(0,t+at);g.gain.linearRampToValueAtTime(vol||.12,t+at+.02);g.gain.exponentialRampToValueAtTime(.001,t+at+len);
  o.connect(g);g.connect(ac.destination);o.start(t+at);o.stop(t+at+len+.05);});}catch(e){}}
const chime=up=>tones(up?[[523,0,.5],[659,.12,.5],[784,.24,.5],[1046,.36,.7]]:[[392,0,.5],[330,.14,.5],[262,.28,.8]]);
const coinSnd=()=>tones([[1318,0,.12],[1760,.07,.25]],'square',.05);
/* ---------- background music: two calm folk tracks, cross-faded one into the other ---------- */
const MUS_VOL=[0,.22,.45];
// soft wooden click for every button press
const clickSnd=()=>{if(!audio()||!save.set.snd)return;try{const t=ac.currentTime,o=ac.createOscillator(),g=ac.createGain();
  o.type='sine';o.frequency.setValueAtTime(1400,t);o.frequency.exponentialRampToValueAtTime(700,t+.06);
  g.gain.setValueAtTime(0,t);g.gain.linearRampToValueAtTime(.07,t+.006);g.gain.exponentialRampToValueAtTime(.001,t+.08);
  o.connect(g);g.connect(ac.destination);o.start(t);o.stop(t+.1);}catch(e){}};
document.addEventListener('pointerdown',e=>{const b=e.target.closest&&e.target.closest('button');if(b&&!b.disabled)clickSnd();},true);
const CHEST_COINS=30,SUIT_NAME_RU={s:'пики ♠',c:'трефы ♣',h:'червы ♥',d:'бубны ♦'};
// embedded tracks are decoded by hand: some pages forbid fetch() even for data: addresses
function bytesOf(u){if(u.startsWith('data:')){const bin=atob(u.slice(u.indexOf(',')+1)),a=new Uint8Array(bin.length);for(let i=0;i<bin.length;i++)a[i]=bin.charCodeAt(i);return Promise.resolve(a.buffer);}
  return fetch(u).then(r=>r.arrayBuffer());}
const music={bufs:null,loading:false,gain:null,idx:0,src:null,timer:0,
  vol(){return MUS_VOL[save.set.mus]||0;},
  load(){if(this.bufs||this.loading||!audio()||!(window.__MUSIC||[]).length)return;this.loading=true;
    Promise.all(window.__MUSIC.map(u=>bytesOf(u).then(b=>new Promise((ok,no)=>ac.decodeAudioData(b,ok,no)))))
      .then(bs=>{this.bufs=bs;this.loading=false;this.update();}).catch(()=>{this.loading=false;});},
  // the next track is started by the audio clock, not by a timer: when the tab is hidden the clock stops,
  // so a timer cannot fire early and lay one tune over the other
  play(){if(!this.bufs||this.src)return;const b=this.bufs[this.idx%this.bufs.length],s=ac.createBufferSource(),t=ac.currentTime,fade=2.5;
    if(!this.gain){this.gain=ac.createGain();this.gain.connect(ac.destination);}
    const g=ac.createGain();g.gain.setValueAtTime(0,t);g.gain.linearRampToValueAtTime(1,t+fade);g.gain.setValueAtTime(1,t+b.duration-fade-1);g.gain.linearRampToValueAtTime(0,t+b.duration-1);
    s.buffer=b;s.connect(g);g.connect(this.gain);s.start(t);s.stop(t+b.duration);this.src=s;this.nextAt=t+b.duration-fade-1;
    if(!this.timer)this.timer=setInterval(()=>{if(this.src&&ac.state==='running'&&ac.currentTime>=this.nextAt){this.src=null;this.idx++;this.play();}},500);},
  update(){const v=this.vol();if(!v){if(this.gain)this.gain.gain.setTargetAtTime(0,ac.currentTime,.3);return;}
    if(!this.bufs){this.load();return;}if(!this.src)this.play();this.gain.gain.setTargetAtTime(v,ac.currentTime,.4);}
};
// the first tap anywhere starts the music (browsers only allow sound after a user action)
addEventListener('pointerdown',()=>{if(save.set.mus)music.update();},{passive:true});
document.addEventListener('visibilitychange',()=>{if(!ac)return;if(document.hidden)ac.suspend();else{ac.resume().catch(()=>{});if(save.set.mus)music.update();}});
// iPhone browsers freeze sound when the app goes to the background; the next touch brings it back
['touchend','pointerup','keydown'].forEach(ev=>addEventListener(ev,()=>{if(ac&&ac.state!=='running'){audio();if(save.set.mus)music.update();}},{passive:true,capture:true}));
addEventListener('pageshow',()=>{if(ac&&ac.state!=='running')ac.resume().catch(()=>{});});

/* ---------- navigation ---------- */
const SCREENS=['home','camp','quick','shop','stats','table','friends','lobby'];
function show(id){for(const s of SCREENS)$(s).hidden=s!==id;refreshCoins();fxSync();
  if(id==='home')renderHome();if(id==='camp')renderCamp();if(id==='quick')renderQuick();if(id==='shop')renderShop();if(id==='stats')renderStats();if(id==='friends')renderFriends();}
document.querySelectorAll('[data-go]').forEach(b=>b.onclick=()=>show(b.dataset.go));
menuFx.attach(document.querySelector('#home .hdeco'));
function fxSync(){menuFx.set(save.tableSkin);menuFx.run(save.set.fx&&!$('home').hidden);}
function modal(id,on){$(id).hidden=!on;}
let lastCoins=null;
function refreshCoins(){document.querySelectorAll('.coinVal').forEach(e=>e.textContent=save.coins);
  if(lastCoins!=null&&save.coins>lastCoins)document.querySelectorAll('.coins').forEach(e=>{e.classList.remove('bump');void e.offsetWidth;e.classList.add('bump');});lastCoins=save.coins;
  const hs=document.getElementById('homeStars');if(hs)hs.textContent='★ '+starsTotal()+' / '+LOCS.reduce((a,l)=>a+l.stages.length*3,0);}
function addCoins(n){if(!n)return;save.coins+=n;save.st.coinsEarned+=Math.max(0,n);persist();refreshCoins();}
const portrait=id=>id==='you'?PORTRAITS.you:CHR(id).pic;
function CHR(id){return CHARS[id]||netChar(id);}
// a line of speech in quotes, or nothing for people (only characters talk)
const ql=(id,k)=>{const t=charLine(id,k);return t?`«${t}»`:'';};

/* ---------- toasts (achievements) ---------- */
const toastQ=[];let toastOn=false;
function toast(t,s){toastQ.push([t,s]);if(!toastOn)nextToast();}
function nextToast(){const it=toastQ.shift();if(!it){toastOn=false;return;}toastOn=true;$('toastT').textContent=it[0];$('toastS').textContent=it[1];
  $('achToast').classList.add('on');coinSnd();setTimeout(()=>{$('achToast').classList.remove('on');setTimeout(nextToast,400);},2600);}
function checkAch(){for(const a of newAch()){save.ach[a.id]=Date.now();addCoins(a.c);toast('Достижение: '+a.name,a.d+' · +'+a.c+' монет');}persist();}

/* ---------- home ---------- */
function renderFan(){setFaceStyle(save.face);$('fan').innerHTML=[['Д','h',-22],['К','s',0],['Т','d',22]].map(([r,su,a],i)=>`<div class="fc" style="transform:rotate(${a}deg);animation-delay:${i*.08}s">${faceSVG({r,s:su})}</div>`).join('');}
renderFan();$('table').insertAdjacentHTML('afterbegin',TDECO_HTML);
function renderHome(){const st=starsTotal(),cur=LOCS.findIndex((l,i)=>!locDone(i));
  $('homeProg').textContent=`Звёзд в походе: ${st} из ${STARS_MAX}`+(cur<0?' · Поход пройден!':` · Сейчас: ${LOCS[cur].name}`);
  renderDaily();checkGift();}
function renderDaily(){const d=dailyTask(),done=dailyDone(),b=$('hDaily');
  $('dailyT').textContent=`${MODE_NAME[d.mode]}, ${plural(d.deck,'карта','карты','карт')}, ${plural(d.players-1,'соперник','соперника','соперников')}: ${goalInfo(d.goal).d}`;
  $('dailyR').innerHTML=done?'✓ Выполнено':'<span class="coin">₽</span> +'+DAILY_REWARD;b.classList.toggle('done',done);b.disabled=done;}
$('hDaily').onclick=()=>{if(dailyDone())return;audio();const d=dailyTask();
  startGame({kind:'daily',opps:pickOpps('medium',d.players-1),mode:d.mode,deck:d.deck,level:'medium',goals:['win',d.goal],skin:save.tableSkin});};
$('hCamp').onclick=()=>{audio();show('camp');};
$('hQuick').onclick=()=>{audio();show('quick');};
$('hShop').onclick=()=>show('shop');
$('hStats').onclick=()=>show('stats');
$('hSet').onclick=()=>openSettings();
$('hRules').onclick=()=>modal('rules',true);
$('rulesDone').onclick=()=>modal('rules',false);
function checkGift(){const today=dayKey();if(save.gift.day===today)return;
  const y=new Date(Date.now()-864e5),yk=y.getFullYear()+'-'+(y.getMonth()+1)+'-'+y.getDate();
  const streak=save.gift.day===yk?Math.min(save.gift.streak+1,GIFTS.length):1,amount=GIFTS[streak-1];
  $('giftP').textContent=streak>1?`Вы заходите ${plural(streak,'день','дня','дней')} подряд — подарок растёт.`:'Заходите каждый день — подарок будет расти.';
  $('giftRow').innerHTML=GIFTS.map((g,i)=>`<span style="display:inline-flex;flex-direction:column;align-items:center;gap:2px;font-size:11px;color:${i<streak?'#8a5d16':'#b7ab92'}"><span class="coin" style="width:26px;height:26px;opacity:${i<streak?1:.45}">₽</span>${g}</span>`).join('');
  $('giftTake').dataset.amount=amount;
  $('giftTake').onclick=()=>{save.gift={day:today,streak};addCoins(amount);coinSnd();modal('giftM',false);toast('Подарок дня','+'+amount+' монет');};
  modal('giftM',true);}

/* ---------- campaign ---------- */
function stageName(st){return st.name||(st.opps.length===1?CHARS[st.opps[0]].name:st.opps.map(o=>CHARS[o].name.split(' ').pop()).join(', '));}
function starsHtml(arr){return `<span class="stars">${arr.map(v=>`<span class="${v?'on':''}">★</span>`).join('')}</span>`;}
const LOCK='<svg width="12" height="14" viewBox="0 0 12 14" aria-label="закрыто"><rect x="1" y="6" width="10" height="8" rx="2" fill="currentColor"/><path d="M3.5 6V4.5a2.5 2.5 0 0 1 5 0V6" stroke="currentColor" stroke-width="1.6" fill="none"/></svg>';
function renderCamp(){
  $('campStars').textContent=`Звёзд: ${starsTotal()} из ${STARS_MAX}`;
  $('locs').innerHTML=LOCS.map((L,li)=>{const open=locOpen(li);
    const nodes=L.stages.map((st,si)=>{const r=stageRec(L.id,si),ok=stageOpen(li,si);
      return `<button class="node${st.boss?' boss':''}" type="button" data-l="${li}" data-s="${si}" ${ok?'':'disabled'}>
        <span class="faces">${st.opps.slice(0,3).map(o=>`<span>${portrait(o)}</span>`).join('')}</span>
        <span class="nm">${stageName(st)}</span>${ok?starsHtml(r.stars):'<span class="lockicon">'+LOCK+'</span>'}</button>`;}).join('');
    const got=L.stages.reduce((a,s,si)=>a+stageRec(L.id,si).stars.reduce((x,y)=>x+y,0),0);
    return `<section class="panel loc${open?'':' locked'}"><div class="lh"><h3>${li+1}. ${L.name}</h3><span class="stars"><span class="on">★</span>&nbsp;${got}/12</span></div>
      <p class="lrule">${L.rule}</p><p class="story">${open?L.story:'Откроется после победы в «'+stageName(LOCS[li-1].stages[3])+'».'}</p><div class="nodes">${nodes}</div></section>`;}).join('');
  $('locs').querySelectorAll('.node').forEach(b=>b.onclick=()=>openStage(+b.dataset.l,+b.dataset.s));
  // scroll to the current location
  const cur=Math.max(0,LOCS.findIndex((l,i)=>!locDone(i)));const el=$('locs').children[cur];if(el&&cur>0)setTimeout(()=>el.scrollIntoView({block:'center'}),30);
}
// first win pays more the further the place; bosses pay a bonus; replays pay a little
function stageReward(li,si,rec){const st=LOCS[li].stages[si];return rec.won?8+3*li:40+25*li+(st.boss?100+20*li:0);}
function openStage(li,si){const L=LOCS[li],st=L.stages[si],r=stageRec(L.id,si);
  $('smT').textContent=stageName(st);
  $('smOpps').innerHTML=st.opps.map(o=>`<span class="pv"><span class="pic">${portrait(o)}</span><small>${CHARS[o].name}</small></span>`).join('');
  const rl=Object.keys(st.rules||{}).map(k=>RULE_TEXT[k]).filter(Boolean);
  $('smMeta').innerHTML=`<span>${MODE_NAME[st.mode]}</span><span>${st.deck===54?'54 с джокерами':plural(st.deck,'карта','карты','карт')}</span><span>${plural(st.opps.length+1,'игрок','игрока','игроков')}</span>`+rl.map(x=>`<span class="rule">${x}</span>`).join('');
  $('smGoals').innerHTML=st.goals.map((k,i)=>`<div><span class="st ${r.stars[i]?'on':''}">★</span>${GOALS[k].t}</div>`).join('');
  $('smRw').textContent=r.won?`Повторная победа: +${stageReward(li,si,r)} монет, за каждую новую звезду ещё +10.`:`Награда за первую победу: +${stageReward(li,si,r)} монет и +10 за каждую звезду.`;
  $('smPlay').onclick=()=>{modal('stageM',false);startGame({kind:'camp',li,si,opps:st.opps,mode:st.mode,deck:st.deck,goals:st.goals,skin:L.table,rules:st.rules||{}});};
  modal('stageM',true);$('smPlay').focus();}
$('smClose').onclick=()=>modal('stageM',false);

/* ---------- quick game ---------- */
const POOLS={1:['vanka','kuzmich'],2:['nura','tishka','matryona','prokhor','aglaya','erofey','pelageya','mitrofan'],3:['kupets','akim','voevoda','klyuchnitsa','foma','bayun','leshy','alesha','dobrynya','varvara','kikimora'],4:['boyarin','nesmeyana','yaga','ilya','gorynych']};
const LEVELS={easy:{name:'Лёгкие',mult:1,from:[1,2]},medium:{name:'Средние',mult:1.5,from:[2,1]},hard:{name:'Сильные',mult:2.2,from:[3,4,2]},mixed:{name:'Вперемешку',mult:1.6,from:'mix'}};
let quickOpps=[];
function pickOpps(level,k){const L=LEVELS[level];let pool=[];
  if(L.from==='mix')pool=[...POOLS[1],...POOLS[2],...POOLS[3]].sort(()=>Math.random()-.5);
  else for(const lv of L.from)pool.push(...POOLS[lv].slice().sort(()=>Math.random()-.5));
  if(level==='hard'&&stageRec('koschei',3).won)pool.unshift('koschei');
  if(level==='hard'&&stageRec('palace',2).won)pool.unshift('tsar');
  return pool.slice(0,k);}
function segButtons(el,opts,cur,onPick){el.innerHTML=opts.map(([v,t,dis])=>`<button type="button" aria-pressed="${v===cur}" ${dis?'disabled':''} data-v="${v}">${t}</button>`).join('');
  el.querySelectorAll('button').forEach(b=>b.onclick=()=>onPick(isNaN(+b.dataset.v)?b.dataset.v:+b.dataset.v));}
function renderQuick(reroll){const q=save.quick;if(q.deck===54){q.deck=52;q.jokers=true;}if(!q.rules)q.rules={};
  const maxOpp=q.deck===24?3:q.deck===36?4:5;if(q.players-1>maxOpp)q.players=maxOpp+1;
  segButtons($('qDeck'),[[24,'24'],[36,'36'],[52,'52']],q.deck,v=>{q.deck=v;persist();renderQuick();});
  $('qJokRow').hidden=q.deck!==52;
  segButtons($('qJok'),[[0,'Без джокеров'],[1,'С джокерами']],q.jokers?1:0,v=>{q.jokers=!!v;persist();renderQuick();});
  // q.players counts the whole table (you + opponents); the buttons above show opponents only
  const RL=[['neighbors','Подкидывают только соседи',q.players<3,'от 2 соперников'],['show','Перевод показом козыря',q.mode!=='perevodnoy','в переводном'],
    ['noLimit','Без лимита подкидывания',false,''],['teams','Пара на пару',q.players!==4,'ровно 3 соперника']];
  $('qRules').innerHTML=RL.map(([k,t,dis,need])=>`<button type="button" aria-pressed="${!!q.rules[k]&&!dis}" ${dis?'disabled':''} data-k="${k}">${t}${dis&&need?` <small>(${need})</small>`:''}</button>`).join('');
  $('qRules').querySelectorAll('button').forEach(b=>b.onclick=()=>{q.rules[b.dataset.k]=!q.rules[b.dataset.k];persist();renderQuick();});
  segButtons($('qPlayers'),[1,2,3,4,5].map(k=>[k+1,String(k),k>maxOpp]),q.players,v=>{q.players=v;persist();renderQuick(true);});
  segButtons($('qMode'),[['podkidnoy','Подкидной'],['perevodnoy','Переводной']],q.mode,v=>{q.mode=v;persist();renderQuick();});
  segButtons($('qLevel'),Object.entries(LEVELS).map(([k,v])=>[k,v.name]),q.level,v=>{q.level=v;persist();renderQuick(true);});
  if(reroll||quickOpps.length!==q.players-1)quickOpps=pickOpps(q.level,q.players-1);
  $('qPreview').innerHTML=quickOpps.map(o=>`<span class="pv"><span class="pic">${portrait(o)}</span><small>${CHARS[o].name}</small></span>`).join('');
  $('qHint').textContent=`Победа: +${quickReward(q.players-1,q.level)} монет. `+(q.deck===24?'Короткая колода от девятки до туза — быстрые партии.':q.deck===52?(q.jokers?'52 карты с двойками и два джокера — джокер бьёт любую карту.':'Большая колода от двойки до туза.'):'Классическая колода от шестёрки до туза.');}
function quickRules(q){const r={};for(const k in (q.rules||{}))if(q.rules[k])r[k]=true;if(q.players<3)delete r.neighbors;if(q.players!==4)delete r.teams;if(q.mode!=='perevodnoy')delete r.show;return r;}
const quickReward=(k,level)=>Math.round(8*k*LEVELS[level].mult+6);
$('qPlay').onclick=()=>{audio();const q=save.quick;startGame({kind:'quick',opps:quickOpps.slice(),mode:q.mode,deck:q.deck===52&&q.jokers?54:q.deck,level:q.level,goals:null,skin:save.tableSkin,rules:quickRules(q)});};

/* ---------- shop ---------- */
let shopTab='backs';
$('tbBacks').onclick=()=>{shopTab='backs';renderShop();};$('tbTables').onclick=()=>{shopTab='tables';renderShop();};$('tbFaces').onclick=()=>{shopTab='faces';renderShop();};
function tablePreview(id){
  return `<div class="tprev skin-${id}" style="${id==='izba'?'':'background:'+TABLE_BG[id]}${id==='palaty'?';box-shadow:inset 0 0 0 5px #b7832a,0 4px 10px rgba(0,0,0,.25)':''}">${TDECO_HTML}</div>`;}
const FACE_SAMPLE=[{r:'Т',s:'h'},{r:'К',s:'s'},{r:'7',s:'d'}];
function renderShop(){
  $('tbBacks').setAttribute('aria-selected',String(shopTab==='backs'));$('tbTables').setAttribute('aria-selected',String(shopTab==='tables'));$('tbFaces').setAttribute('aria-selected',String(shopTab==='faces'));
  const list=SHOP[shopTab],cur=shopTab==='backs'?save.back:shopTab==='faces'?save.face:save.tableSkin;
  $('shopGrid').innerHTML=list.map(it=>{const own=save.owned.includes(it.id);
    const prev=shopTab==='backs'?`<div class="prev">${backSVG(it.id)}</div>`:shopTab==='faces'?`<div class="fprev">${FACE_SAMPLE.map(c=>faceSVG(c,it.id)).join('')}</div>`:tablePreview(it.id);
    let btn;if(cur===it.id)btn=`<div class="sel">✓ Выбрано</div>`;else if(own)btn=`<button class="gold" data-eq="${it.id}" type="button">Выбрать</button>`;
    else if(it.price<0)btn=`<button class="gold" disabled type="button">Награда</button>`;
    else btn=`<button class="gold" data-buy="${it.id}" type="button" ${save.coins<it.price?'disabled':''}><span style="display:inline-flex;gap:6px;align-items:center"><span class="coin">₽</span>${it.price}</span></button>`;
    return `<div class="panel item">${prev}<h4>${it.name}</h4>${it.d?`<div class="d">${it.d}</div>`:''}<div class="how">${it.price<0&&!own?it.how+(it.id==='morozko'?` (${Math.min(save.st.dailyCount||0,7)} из 7)`:''):own?'В коллекции':''}</div>${btn}</div>`;}).join('');
  $('shopGrid').querySelectorAll('[data-buy]').forEach(b=>b.onclick=()=>{const it=list.find(x=>x.id===b.dataset.buy);if(save.coins<it.price)return;
    save.coins-=it.price;save.owned.push(it.id);equip(it.id);coinSnd();checkAch();renderShop();});
  $('shopGrid').querySelectorAll('[data-eq]').forEach(b=>b.onclick=()=>{equip(b.dataset.eq);renderShop();});
  refreshCoins();}
function equip(id){if(shopTab==='backs')save.back=id;else if(shopTab==='faces'){save.face=id;renderFan();}else save.tableSkin=id;persist();applySkin();}
// menus wear the same cloth as the chosen table
function applySkin(){if(typeof fxSync==='function'&&$('home'))fxSync();document.querySelectorAll('.mscreen').forEach(e=>{e.className=e.className.replace(/\bskin-\S+/g,'').trim()+' skin-'+save.tableSkin;});
  document.body.style.background=getComputedStyle($('home')).getPropertyValue('--felt-deep')||'';}
applySkin();

/* ---------- stats ---------- */
let statTab='st';
$('tbSt').onclick=()=>{statTab='st';renderStats();};$('tbAch').onclick=()=>{statTab='ach';renderStats();};
function pct(w,g){return g?Math.round(w/g*100)+'%':'—';}
function renderStats(){const s=save.st;
  $('tbSt').setAttribute('aria-selected',String(statTab==='st'));$('tbAch').setAttribute('aria-selected',String(statTab==='ach'));
  if(statTab==='ach'){const S=achStats(),done=ACH.filter(a=>save.ach[a.id]).length;
    $('statBody').innerHTML=`<p class="sub" style="text-align:center;margin:0">Получено ${done} из ${ACH.length}</p>`+ACH.map(a=>`<div class="panel ach${save.ach[a.id]?' done':''}"><span class="medal">${save.ach[a.id]?'★':'☆'}</span><div><h4>${a.name}</h4><p>${a.d}</p></div><span class="rw">+${a.c}</span></div>`).join('');return;}
  const tile=(v,l)=>`<div class="panel tile"><b>${v}</b><span>${l}</span></div>`;
  const row=(name,o)=>`<div class="brow"><span>${name}</span><em>${o.g||0} игр</em><span>${pct(o.w||0,o.g||0)}</span></div>`;
  const byP=[2,3,4,5,6].filter(n=>s.byPlayers[n]).map(n=>row(plural(n,'игрок','игрока','игроков'),s.byPlayers[n])).join('')||'<div class="brow"><span>Пока нет партий</span><em></em><span></span></div>';
  $('statBody').innerHTML=`<div class="tiles">${tile(s.games,'партий')}${tile(s.wins,'побед')}${tile(s.losses,'раз в дураках')}${tile(pct(s.wins,s.games),'побед от всех партий')}
    ${tile(s.bestStreak,'лучшая серия побед')}${tile(s.streak,'текущая серия')}${tile(s.pogGiven,'погон повешено')}${tile(s.pogGot,'погон получено')}
    ${tile(s.firstOuts,'раз вышли первым')}${tile(s.transfers,'переводов')}${tile(s.takes,'раз брали карты')}${tile(s.coinsEarned,'монет заработано')}</div>
    <div class="panel breakdown"><h4>Правила</h4>${row('Подкидной',s.byMode.podkidnoy)}${row('Переводной',s.byMode.perevodnoy)}</div>
    <div class="panel breakdown"><h4>Колода</h4>${[[24,'24 карты'],[36,'36 карт'],[52,'52 карты'],[54,'54 с джокерами']].filter(([k])=>s.byDeck[k]&&s.byDeck[k].g||k===36).map(([k,t])=>row(t,s.byDeck[k]||{g:0,w:0})).join('')}</div>
    <div class="panel breakdown"><h4>Игроков за столом</h4>${byP}</div>
    <div class="panel breakdown"><h4>Царский путь</h4><div class="brow"><span>Звёзд собрано</span><em></em><span>${starsTotal()} / ${STARS_MAX}</span></div><div class="brow"><span>Локаций пройдено</span><em></em><span>${locsDone()} / ${LOCS.length}</span></div></div>`;}

/* ---------- settings / pause ---------- */
const SETS=[
  {k:'hl',lbl:'Подсветка карт',hint:'Выделять карты, которыми можно сходить',opts:[[true,'Вкл'],[false,'Выкл']]},
  {k:'sort',lbl:'Порядок карт в руке',hint:'Как раскладывать руку',opts:[['suit','По мастям'],['rank','По старшинству']]},
  {k:'trumpEnd',lbl:'Козыри отдельно',hint:'Держать козыри в правом краю руки',opts:[[true,'Да'],[false,'Нет']]},
  {k:'speed',lbl:'Скорость карт',hint:'Насколько неспешно двигаются карты',opts:[['fast','Быстро'],['normal','Обычно'],['slow','Плавно']]},
  {k:'snd',lbl:'Звуки',hint:'Карты, монеты, победа',opts:[[true,'Вкл'],[false,'Выкл']]},
  {k:'mus',lbl:'Музыка',hint:'Народные мелодии на фоне',opts:[[0,'Выкл'],[1,'Тихо'],[2,'Громче']]},
  {k:'fx',lbl:'Анимация фона',hint:'Снег, искры, лепестки в меню — под цвет стола',opts:[[1,'Вкл'],[0,'Выкл']]}
];
function openSettings(){renderSettings();modal('settings',true);$('setDone').focus();}
function renderSettings(){
  $('setRows').innerHTML=SETS.map((s,i)=>`<div class="setrow"><div class="lbl">${s.lbl}${s.hint?`<small>${s.hint}</small>`:''}</div><div class="seg" role="group" aria-label="${s.lbl}">`+
    s.opts.map(([v,t],j)=>`<button type="button" id="set${i}_${j}" data-i="${i}" data-j="${j}" aria-pressed="${save.set[s.k]===v}">${t}</button>`).join('')+`</div></div>`).join('');
  $('setRows').querySelectorAll('button').forEach(b=>b.onclick=()=>{const s=SETS[+b.dataset.i];save.set[s.k]=s.opts[+b.dataset.j][0];persist();applySpeed();renderSettings();if(s.k==='mus')music.update();if(s.k==='fx')fxSync();if(g)layout();});
}
$('setDone').onclick=()=>modal('settings',false);
let paused=false;
$('toMenu').onclick=()=>{if(!g)return;$('pNew').hidden=!!NET;$('pWarn').hidden=!counts();$('pWarn').textContent=NET?'Если выйти, партия засчитается как поражение, а за вас доиграет бот.':'Если начать заново или выйти, партия засчитается как поражение.';if(NET){modal('pause',true);$('pResume').focus();return;}paused=true;stopTimer();clearTimeout(botT);botThinking=false;if(extraPending){extraPending=false;anim=false;}modal('pause',true);$('pResume').focus();};
function resume(){modal('pause',false);paused=false;if(g&&!g.over&&!anim)proceed();}
$('pResume').onclick=resume;
$('pSet').onclick=()=>openSettings();
$('pRules').onclick=()=>modal('rules',true);
$('pNew').onclick=()=>{modal('pause',false);paused=false;forfeit();startGame(cfg);};
$('pExit').onclick=()=>{modal('pause',false);paused=false;if(NET)return netLeave();leaveGame();};
addEventListener('keydown',e=>{if(e.key!=='Escape')return;
  for(const id of ['rules','settings','stageM'])if(!$(id).hidden){modal(id,false);return;}
  if(!$('pause').hidden){resume();return;}
  if(!$('table').hidden&&$('over').hidden)$('toMenu').click();});

/* ---------- game ---------- */
const table=$('table');
let lastWin=0,NET=false,g=null,cfg=null,seatChar=[],els={},anim=false,botT=0,botThinking=false,target=-1,pending=null;
let masked=[],ghost=null,track=null,fastFwd=false,gen=0,myRun=false,extraPending=false,RU={},cheatSeen=-1,trumpSeen=true,chestCard=null,tmrT=0,tmrLeft=0;
function clearAll(){gen++;stopTimer();clearTimeout(botT);botThinking=false;anim=false;fastFwd=false;myRun=false;extraPending=false;Object.values(els).forEach(e=>e.remove());els={};g=null;$('seats').innerHTML='';}
function leaveGame(){forfeit();const back=cfg&&cfg.kind==='camp'?'camp':cfg&&cfg.kind==='online'?'friends':'quick';clearAll();modal('over',false);show(back);}
function startGame(c){
  cfg=c;clearAll();modal('over',false);$('overMain').disabled=false;show('table');setFaceStyle(save.face);
  const M=c.mirror,fresh=!M||c.fresh;if(fresh)shuffleSnd();
  table.className='screen skin-'+(c.skin||'sukno');
  seatChar=M?netSeatChars():['you',...c.opps];
  RU=c.rules||{};trumpSeen=!RU.dark;
  g=M?M.g:new Game({mode:c.mode,deck:c.deck,players:c.opps.length+1,teams:RU.teams&&c.opps.length===3?[0,1,0,1]:null,rules:{neighbors:!!RU.neighbors,show:!!RU.show,noLimit:!!RU.noLimit,cheat:!!RU.cheat}});g.events=[];
  track={takes:0,transfers:0,lastOuts:[],chest:false,cheats:0,caught:0,missed:0};cheatSeen=-1;
  for(const cd of [...g.deck,...g.hands.flat(),...g.table.flatMap(x=>x.d?[x.a,x.d]:[x.a]),...g.discard])els[cd.id]=mkCard(cd);
  if(M)chestCard=M.chest;
  else if(RU.chest){const pool=g.deck.filter(x=>x!==g.trumpCard);chestCard=pool[Math.floor(Math.random()*pool.length)];}else chestCard=null;
  if(chestCard&&els[chestCard.id])els[chestCard.id].classList.add('chest');
  if(M&&!trumpSeen&&(g.deck.length===0||g.discard.some(x=>x.s===g.trump)))trumpSeen=true;
  buildSeats();target=-1;pending=null;$('skipOut').hidden=true;$('chatBtn').hidden=!M;$('chatP').hidden=true;
  masked=[];if(fresh)for(let i=0;i<6;i++)for(let p=0;p<g.n;p++)if(g.hands[p][i])masked.push(g.hands[p][i]);
  anim=true;ghost=null;renderGoals();layout(true);updateControls();
  const my=gen;
  if(!fresh){anim=false;proceed();return;}
  setTimeout(()=>{if(my===gen)reveal(Math.max(50,300/g.n),()=>{const bots=seatChar.map((id,p)=>CHARS[id]&&p>0?p:-1).filter(p=>p>0);
    if(bots.length){const sp=bots[Math.floor(Math.random()*bots.length)];say(sp,charLine(seatChar[sp],'start'));}anim=false;proceed();});},350);
}
function mkCard(c){const e=document.createElement('div');e.className='card down';
  e.innerHTML=`<div class="in"><div class="f">${faceSVG(c)}</div><div class="b">${backSVG(save.back)}</div></div>`;
  e.addEventListener('click',()=>{if(Date.now()-dragEnd<350)return;onCard(c);});e.addEventListener('pointerdown',ev=>dragStart(ev,c,e));e.setAttribute('aria-label',c.r==='J'?(c.s==='r'?'красный джокер':'чёрный джокер'):c.r+' '+SUIT_NAME[c.s]);table.appendChild(e);return e;}
function reveal(step,done){const my=gen;if(!masked.length)return done();masked.shift();flick(.12);layout();setTimeout(()=>{if(my===gen)reveal(step,done);},step*SP());}
function buildSeats(){const k=g.n-1;
  $('seats').innerHTML=seatChar.slice(1).map((id,i)=>`<div class="seat${k>1?' col':''}${g.mate(0,i+1)?' mate':''}" id="seat${i+1}"><div class="ava">${portrait(id)}<span class="role"></span>${g.mate(0,i+1)?'<span class="mtag">напарник</span>':''}</div>
    <div class="txt"><div class="nm" title="${CHR(id).name}">${k>1?CHR(id).short:CHR(id).name}</div><div class="inf"></div></div><div class="bubble off"></div></div>`).join('');}
function renderGoals(){const el=$('goals');if(!cfg.goals){el.innerHTML='';return;}
  el.innerHTML=cfg.goals.map(k=>`<span data-k="${k}">${GOALS[k].short}</span>`).join('');}
function goalFailed(key){if(!g)return false;const {k,n}=goalParse(key);switch(k){case'take':return track.takes>n;case'fast':return g.bouts>n;
  case'first':return g.out.length>0&&g.out[0]!==0;case'win':return g.over&&g.fool===0;}return false;}

/* ---------- layout ---------- */
let W,H,CW,CH,PORT,SHORT,handY=0;
function measure(){W=table.clientWidth;H=table.clientHeight;PORT=W<H*.8;SHORT=!PORT&&H<520;
  CW=Math.round(PORT?Math.max(54,Math.min(W/5.3,H/7.4,100)):Math.max(54,Math.min(W/7.2,H/6.4,112)));CH=Math.round(CW*1.4);
  table.style.setProperty('--cw',CW+'px');table.style.setProperty('--ch',CH+'px');}
function place(c,x,y,r,z,up,s){const e=els[c.id];s=s||1;if(c.ph)up=false; // a card not known yet stays face down
  e.style.transform=`translate(${x-CW*(1-s)/2}px,${y-CH*(1-s)/2}px) rotate(${r||0}deg) scale(${s})`;e.style.zIndex=z;e.classList.toggle('down',!up);e.classList.toggle('mini',s<1);}
const suitIcon=s=>`<svg viewBox="0 0 10 10">${suitShape(s,5,5,10,false,RED[s]?'#e0474d':'#f6efe0')}</svg>`;
function clean(c,...keep){const e=els[c.id];for(const k of ['stack','play','dim','target','pick'])if(!keep.includes(k))e.classList.remove(k);}
function layout(instant){
  if(!g)return;measure();
  const pad=Math.max(16,W*.03),hidden=new Set(masked),k=g.n-1,safeTop=16;
  const gh=ghost?new Set(ghost.flatMap(x=>x.d?[x.a,x.d]:[x.a])):new Set();
  const py=H-CH-Math.max(14,H*.03);handY=py;
  // ---- opponents
  let topBottom;
  if(k===1){
    const botY=PORT?92:78-CH*.55;topBottom=botY+CH;
    const seat=$('seat1');seat.style.cssText=`left:${pad}px;top:${safeTop}px;--av:52px`;
    seatHand(1,W/2,botY,0,1,hidden,gh,false);
  }else{
    const av=PORT?38:46,sw=Math.min(130,(W-2*pad)/k),seatTop=54,s=PORT?(k>=4?.32:.4):Math.min(.55,sw/(CW*1.6)),gap=PORT?44:44;
    for(let i=1;i<=k;i++){const cx=pad+(i-.5)*(W-2*pad)/k;const seat=$('seat'+i);
      seat.style.cssText=`left:${cx-sw/2}px;top:${seatTop}px;--av:${av}px;--sw:${sw}px`;seat.classList.toggle('rt',cx>W*.62);seat.classList.toggle('lt',cx<W*.38);
      seatHand(i,cx,seatTop+av+gap,Math.min(sw*.8,CW*s*.9),s,hidden,gh,true);}
    topBottom=seatTop+av+gap+CH*s;
  }
  // seat states
  for(let p=1;p<g.n;p++){const seat=$('seat'+p);if(!seat)continue;const out=!g.active(p);
    seat.classList.toggle('att',!g.over&&!out&&p===g.att&&!anim);seat.classList.toggle('def',!g.over&&!out&&p===g.def&&!anim);
    seat.classList.toggle('out',out);seat.classList.toggle('fool',g.over&&g.fool===p);
    const tmv=g.over?-1:g.toMove();seat.querySelector('.role').textContent=p===g.def?(g.taking?'берёт':'бьётся'):(g.table.length&&p===tmv&&!anim)?'подкидывает':p===g.att?'ходит':'';
    const cnt=g.hands[p].filter(c=>!hidden.has(c)&&!gh.has(c)).length;
    seat.querySelector('.inf').textContent=out?(g.out.indexOf(p)+1)+' место':RU.fog&&!g.over?'карт: ?':'карт: '+cnt;}
  // ---- deck & discard row
  const sideY=PORT?topBottom+(k===1?22:14):Math.max(H*.44-CH/2,topBottom+10);
  const dx=pad+CW*.05,dy=sideY,tx=dx+CW*.42,ty=dy+(CH-CW)/2;
  const pile=g.deck.slice().concat(masked.slice().reverse());
  pile.forEach((c,i)=>{clean(c);if(c===g.trumpCard)place(c,tx,ty,90,1,trumpSeen);else place(c,dx-i*.25,dy-i*.25,0,2+i,false);els[c.id].classList.toggle('stack',i<pile.length-1);});
  $('deckInfo').style.cssText=`left:${dx-6}px;top:${dy+CH+8}px;width:${CW*1.5}px`;
  $('deckInfo').innerHTML=`${MODE_NAME[g.mode]} · ${g.deckSize}<br><span id="trumpBadge">Козырь ${trumpSeen?suitIcon(g.trump):'?'}</span><br>`+(pile.length?`в колоде ${pile.length}`:'колода пуста');
  const rx=W-pad-CW,ry=sideY,disc=g.discard.filter(c=>!gh.has(c));
  disc.forEach((c,i)=>{clean(c);place(c,rx+((i*37)%9)-4,ry+((i*53)%9)-4,((i*61)%30)-15,2+i,false);els[c.id].classList.toggle('stack',i<disc.length-1);});
  $('discInfo').style.cssText=`left:${rx-10}px;top:${ry+CH+8}px;width:${CW+20}px`;$('discInfo').textContent=disc.length?`бито · ${disc.length}`:'';
  // ---- table
  const tb=ghost||g.table,ax0=PORT?pad:dx+CW*1.55,ax1=PORT?W-pad:rx-CW*.25,step=CW*1.32,perRow=Math.max(1,Math.min(3,Math.floor((ax1-ax0-CW*1.22)/step)+1));
  const rows=Math.ceil(Math.max(1,tb.length)/perRow),rowH=CH*1.18;
  const ph0=g.hands[0].length,two0=ph0>8&&Math.min(W-pad*2-CW,CW*.78*(ph0-1))/(ph0-1)<CW*.34,hy0=two0?py-CH*.5:py;
  const tTop=PORT?sideY+CH+44:topBottom+10,tBot=SHORT?hy0-10:hy0-118,midY=(tTop+tBot)/2;
  const defending=!ghost&&!g.over&&g.def===0&&g.toMove()===0&&!anim&&!botThinking;
  tb.forEach((pr,i)=>{const row=Math.floor(i/perRow),col=i%perRow,inRow=Math.min(perRow,tb.length-row*perRow);
    const x=(ax0+ax1)/2-(inRow*step-step+CW*1.22)/2+col*step,y=midY-(rows*rowH)/2+row*rowH+(rowH-CH)/2-CH*.08;
    clean(pr.a);place(pr.a,x,y,-3,10+i*2,true);const ea=els[pr.a.id];
    ea.classList.toggle('target',defending&&!pr.d&&i===target);ea.classList.toggle('pick',defending&&!pr.d);
    if(pr.d){clean(pr.d);place(pr.d,x+CW*.24,y+CH*.16,7,11+i*2,true);}});
  // ---- my hand
  const ph=sortHand(g.hands[0].filter(c=>!hidden.has(c)&&!gh.has(c))),pn=ph.length,maxSpan=Math.min(W-pad*2-CW,CW*.78*Math.max(0,pn-1)),px0=W/2-maxSpan/2-CW/2;
  const twoRows=pn>8&&maxSpan/(pn-1)<CW*.34;
  if(!twoRows)ph.forEach((c,i)=>{clean(c,'play','dim');const t=pn>1?i/(pn-1)-.5:0;place(c,px0+(pn>1?i*maxSpan/(pn-1):0),py+t*t*CH*.35,t*16,100+i,true);});
  else{const n1=Math.ceil(pn/2);[ph.slice(0,n1),ph.slice(n1)].forEach((row,ri)=>{const n=row.length,span=Math.min(W-pad*2-CW,CW*.78*Math.max(0,n-1)),x0=W/2-span/2-CW/2;
    row.forEach((c,i)=>{clean(c,'play','dim');place(c,x0+(n>1?i*span/(n-1):0),py-(ri?0:CH*.5),0,100+ri*50+i,true);});});}
  markPlayable();
  // ---- controls
  const hy=twoRows?py-CH*.5:py;handY=hy; // top edge of the hand
  if(SHORT){const cx=W-pad-Math.max(100,CW*1.2);$('status').style.cssText=`top:${hy-18}px;left:${cx}px;max-width:${2*(W-cx-10)}px`;$('acts').style.cssText=`top:${hy+28}px;left:${cx}px`;$('goals').style.cssText='display:none';}
  else{$('status').style.cssText=`top:${hy-96}px`;$('acts').style.cssText=`top:${hy-62}px`;$('goals').style.cssText=`top:${hy-124}px`;}
  $('skipOut').style.top=(hy-62)+'px';
  if(cfg.goals)$('goals').querySelectorAll('span').forEach(s=>s.classList.toggle('fail',goalFailed(s.dataset.k)));
  if(instant)Object.values(els).forEach(e=>{e.style.transition='none';e.offsetWidth;e.style.transition='';});
}
function seatHand(p,cx,y,span,s,hidden,gh,col){
  const h=g.hands[p].filter(c=>!hidden.has(c)&&!gh.has(c)),n=h.length,w=CW*s,fog=RU.fog&&!g.over,sp=fog?Math.min(n,3)*w*.12:Math.min(col?span:W*(PORT?.42:.5),(col?w*.42:CW*.42)*Math.max(0,n-1));
  // fog: the hand is squared into a pile, so its size cannot be counted
  h.forEach((c,i)=>{clean(c);const t=n>1?i/(n-1)-.5:0;place(c,cx-sp/2-w/2+(n>1?i*sp/(n-1):0),y+(fog?0:Math.abs(t)*(col?4:10)),fog?0:t*-14,100+i,!!g.over||!!RU.open,s);});}
function sortHand(h){const S=save.set,su=c=>c.r==='J'?9:SUITS.indexOf(c.s),tr=c=>c.r==='J'?2:trumpSeen&&g.isTrump(c)?1:0;
  return h.sort((x,y)=>(S.trumpEnd?(tr(x)-tr(y)):0)||(S.sort==='rank'?((g.rk(x)-g.rk(y))||(su(x)-su(y))):((su(x)-su(y))||(g.rk(x)-g.rk(y)))));}
addEventListener('resize',()=>{if(g)layout(true);});

/* ---------- human input ---------- */
function canUse(c,cheat){if(!g||g.over||anim||paused||!g.active(0)||(NET&&netWait()))return false;
  // friends' table with cheating allowed: any card may be laid when it is your turn — if nobody notices
  if(cheat&&NET&&RU.cheat&&g.table.length&&!(g.def!==0&&!myRun&&g.toMove()!==0)&&(g.def===0?g.toMove()===0&&g.undefended().length>0:g.table.length<g.limit&&(g.taking||g.undefended().length<g.hands[g.def].length)))return true;
  // strict turn order: you throw in only on your turn, but you may lay several cards before the defender answers
  if(g.def!==0&&myRun)return g.canAttack(0,c);
  if(botThinking||g.toMove()!==0)return false;
  if(g.def!==0)return g.canAttack(0,c);
  return g.canTransfer(0,c)||g.table.some((x,i)=>g.canDefend(0,c,i));}
function markPlayable(){if(!g)return;const hl=save.set.hl&&!RU.nohint&&(trumpSeen||g.def!==0),active=!g.over&&!anim&&!paused&&g.active(0)&&((!botThinking&&g.toMove()===0)||(myRun&&g.def!==0));
  // only an opening move (empty table, any card goes) is left unmarked; when beating or adding, the frame shows what fits
  const okAll=active&&!g.table.length&&g.hands[0].every(c=>masked.includes(c)||canUse(c));
  g.hands[0].forEach(c=>{const e=els[c.id];if(masked.includes(c)){e.classList.remove('play','dim');return;}const ok=active&&canUse(c);
    e.classList.toggle('play',hl&&ok&&!okAll);e.classList.toggle('dim',hl&&active&&!ok&&g.table.length>0);e.style.cursor=ok?'pointer':'';});}
function shake(c){const e=els[c.id];e.classList.remove('shake');void e.offsetWidth;e.classList.add('shake');}
function onCard(c){
  if(!g||anim||paused||g.over)return;audio();
  const ti=g.table.findIndex(x=>x.a===c);
  if(ti>=0){if(g.def===0&&!g.table[ti].d&&g.toMove()===0&&!botThinking){target=ti;pending=null;layout();updateControls();}return;}
  if(g.hands[0].indexOf(c)<0)return;
  if(!canUse(c,true)){shake(c);return;}
  if(g.def!==0){clearTimeout(botT);botThinking=false;myRun=true;if(NET&&!g.canAttack(0,c))return myDo({t:'ca',c});return myDo({t:'attack',c});}
  const canT=g.canTransfer(0,c),targets=g.table.map((x,i)=>i).filter(i=>g.canDefend(0,c,i));
  if(NET&&RU.cheat&&!canT&&!targets.length){const i=target>=0&&!g.table[target].d?target:g.table.findIndex(x=>!x.d);target=-1;return myDo({t:'cd',c,i});}
  if(target>=0&&targets.includes(target)&&!canT){const i=target;target=-1;return myDo({t:'defend',c,i});}
  if(canT&&targets.length){pending=c;updateControls();return;}
  if(canT){doTransfer(c);return;}
  const i=targets.includes(target)?target:targets[0];target=-1;myDo({t:'defend',c,i});
}
function doTransfer(c){track.transfers++;save.st.transfers++;myDo({t:'transfer',c});}
// my move: played here, or sent to the friends' table and played when the server confirms it
function myDo(m){if(NET){netMove(m);return;}g.apply(0,m);afterAction();}
function setActs(list){const b=[$('act'),$('act2')];b.forEach((x,i)=>{const it=list[i];x.hidden=!it;if(it){x.textContent=it[0];x.onclick=()=>{if(!anim&&!paused){audio();it[1]();}};}});}
function who(p){return p===0?'Вы':g.n>2?CHR(seatChar[p]).short:CHR(seatChar[p]).name;}
function updateControls(){
  const st=$('status');$('catchBtn').hidden=!catchVisible();
  if(!g||g.over||anim){st.textContent='';setActs([]);markPlayable();return;}
  if(!g.active(0)){st.textContent=`Вы вышли — ${g.out.indexOf(0)+1} место. Ждём остальных…`;setActs([]);$('skipOut').hidden=!!NET;markPlayable();return;}
  const tm=g.toMove();
  if(botThinking||tm!==0){
    // throw-ins go strictly in turn (attacker first, then clockwise); the game always waits for you
    const th=g.throwers(),meLater=g.def!==0&&!g.passed.has(0)&&th.indexOf(0)>th.indexOf(tm),then=meLater&&tm!==g.def?' Потом ваша очередь.':'';
    const more=myRun&&g.def!==0&&g.hands[0].some(c=>g.canAttack(0,c));
    st.textContent=tm===g.def&&tm!==0?`${who(tm)} отбивается…`+(more?' Можно подкинуть ещё':'')
      :!g.table.length?`${who(tm)} ходит…`
      :g.taking?`${who(g.def)} берёт, ${who(tm)} подкидывает…${then}`
      :`${who(tm)} решает, подкинуть ли…${then}`;
    setActs([]);markPlayable();return;}
  if(pending){const c=pending;st.textContent='Перевести или побить?';
    setActs([['Перевести',()=>{pending=null;doTransfer(c);}],['Побить',()=>{pending=null;const i=g.table.findIndex((x,k)=>g.canDefend(0,c,k)),j=target>=0&&g.canDefend(0,c,target)?target:i;target=-1;myDo({t:'defend',c,i:j});}]]);return;}
  if(g.def===0){
    const und=g.undefended().length,canT=g.hands[0].some(c=>g.canTransfer(0,c)),canD=g.hands[0].some(c=>g.table.some((x,i)=>g.canDefend(0,c,i)));
    st.textContent=!canD&&!canT?'Нечем крыть':canT?'Отбейтесь или переведите':und>1?'Отбивайтесь (можно выбрать карту на столе)':'Отбивайтесь';
    const shc=g.hands[0].find(c=>g.canShow(0,c));
    const acts=[['Беру',()=>{target=-1;track.takes++;save.st.takes++;myDo({t:'take'});}]];
    if(shc){acts.unshift(['Показать козырь',()=>{track.transfers++;save.st.transfers++;myDo({t:'show',c:shc});}]);st.textContent='Отбейтесь, переведите или покажите козырь';}
    setActs(acts);
  }else if(!g.table.length){st.textContent='Ваш ход: выберите карту';setActs([]);}
  else if(g.taking){st.textContent=`${who(g.def)} берёт. Ваша очередь: подкинете ещё?`;setActs([['Хватит',()=>myDo({t:'done'})]]);}
  else{st.textContent=g.att===0?'Подкиньте или скажите «Бито»':'Ваша очередь: подкиньте или пас';setActs([[g.att===0?'Бито':'Пас',()=>myDo({t:'done'})]]);}
  markPlayable();startTimer();
}
// "on time" challenge: every decision of the player has a time limit; when it runs out the safe move is made
const TURN_SEC=12;
function stopTimer(){clearInterval(tmrT);tmrT=0;$('tmr').hidden=true;}
function startTimer(){if(NET)return;if(!RU.timer||!g||g.over||anim||paused||!g.active(0)||botThinking||g.toMove()!==0||tmrT)return;
  tmrLeft=TURN_SEC;const el=$('tmr');el.hidden=false;el.textContent=tmrLeft;el.classList.remove('low');const my=gen;
  tmrT=setInterval(()=>{if(my!==gen||paused||anim){stopTimer();return;}tmrLeft--;el.textContent=tmrLeft;el.classList.toggle('low',tmrLeft<=4);if(tmrLeft<=3&&tmrLeft>0)tones([[880,0,.06]],'sine',.04);
    if(tmrLeft<=0){stopTimer();timeUp();}},1000);}
function timeUp(){if(!g||g.over||g.toMove()!==0||NET)return;pending=null;
  if(g.def===0){track.takes++;save.st.takes++;g.take(0);}
  else if(!g.table.length){const c=sortHand(g.hands[0].slice()).find(c=>g.canAttack(0,c));g.attack(0,c);}
  else g.done(0);
  gToast('Время вышло');afterAction();}
function gToast(t){const el=$('toast');el.textContent=t;el.classList.remove('on');void el.offsetWidth;el.classList.add('on');}
// a card shown for a moment over a player's seat (shown trump)
function flashCard(c,p){const box=table.getBoundingClientRect();let x=W/2,y=handY-CH*1.2;
  if(p>0){const s=$('seat'+p);if(s){const b=s.getBoundingClientRect();x=b.left-box.left+b.width/2;y=b.bottom-box.top+6;}}
  const d=document.createElement('div');d.className='flash';d.style.cssText=`left:${x-CW/2}px;top:${y}px;width:${CW}px;height:${CH}px`;d.innerHTML=faceSVG(c);table.appendChild(d);setTimeout(()=>d.remove(),1500);}


/* ---------- cheating: Koschei sometimes lays a wrong card; "Поймал!" makes the cheater (or a wrong accuser) pick up the table ---------- */
function catchVisible(){return RU.cheat&&g&&!g.over&&!anim&&!paused&&g.active(0)&&g.table.length>0;}
$('catchBtn').onclick=()=>{if(!catchVisible())return;audio();clearTimeout(botT);botThinking=false;pending=null;
  if(NET){netMove({t:'acc'});return;}
  const ch=g.cheater();g.accuse(0);
  if(ch>=0){track.caught++;gToast(`Поймал! ${CHR(seatChar[ch]).short} забирает карты`);coinSnd();}else{gToast('Обмана не было — карты забираете вы');track.takes++;}
  cheatSeen=-1;afterAction();};
// a bot that cheats: as defender it covers with a card that does not beat; as a thrower it adds a card of another rank
function tryCheat(p,m,P){if(!RU.cheat||!P.cheat||track.cheats>=4||g.cheater()>=0)return false;
  const h=g.hands[p];
  if(m&&m.t==='take'&&p===g.def&&Math.random()<.5){const i=g.table.findIndex(x=>!x.d);if(i<0)return false;const a=g.table[i].a;
    const fake=h.filter(c=>c.r!=='J'&&!g.beats(c,a)&&!g.isTrump(c)).sort((x,y)=>(x.s===a.s?-1:1)-(y.s===a.s?-1:1)||g.rk(x)-g.rk(y))[0];
    if(fake&&g.cheatDefend(p,fake,i)){track.cheats++;return true;}}
  if(m&&m.t==='done'&&p!==g.def&&Math.random()<.22){const rks=g.ranksOnTable();const extra=h.filter(c=>c.r!=='J'&&!rks.has(c.r)&&!g.isTrump(c)).sort((x,y)=>g.rk(x)-g.rk(y))[0];
    if(extra&&g.cheatAttack(p,extra)){track.cheats++;return true;}}
  return false;}


/* ---------- drag a card from the hand onto the table (mouse or finger) ---------- */
let drag=null,dragEnd=0;
function dragStart(ev,c,e){
  if(ev.button>0||!g||g.over||anim||paused||g.hands[0].indexOf(c)<0||!canUse(c,true))return;
  const r=table.getBoundingClientRect(),m=/translate\(([-\d.]+)px,\s*([-\d.]+)px\)/.exec(e.style.transform)||[0,0,0];
  drag={c,e,id:ev.pointerId,sx:ev.clientX,sy:ev.clientY,ox:ev.clientX-r.left-(+m[1]),oy:ev.clientY-r.top-(+m[2]),on:false,r};
  try{e.setPointerCapture(ev.pointerId);}catch(_){}
}
addEventListener('pointermove',ev=>{if(!drag||ev.pointerId!==drag.id)return;
  if(!drag.on){if(Math.hypot(ev.clientX-drag.sx,ev.clientY-drag.sy)<9)return;drag.on=true;drag.e.classList.add('dragging');drag.e.style.zIndex=999;}
  const x=ev.clientX-drag.r.left-drag.ox,y=ev.clientY-drag.r.top-drag.oy;
  drag.e.style.transform=`translate(${x}px,${y}px) rotate(0deg) scale(1.08)`;
  if(g&&g.def===0){const ti=dropTarget(ev);g.table.forEach((pr,i)=>{if(!pr.d)els[pr.a.id].classList.toggle('target',i===ti||(ti<0&&i===target));});}
  ev.preventDefault();},{passive:false});
function dropTarget(ev){if(!g)return -1;let best=-1;
  g.table.forEach((pr,i)=>{if(pr.d)return;const b=els[pr.a.id].getBoundingClientRect(),pad=CW*.25;
    if(ev.clientX>b.left-pad&&ev.clientX<b.right+pad&&ev.clientY>b.top-pad&&ev.clientY<b.bottom+pad)best=i;});return best;}
function dragFinish(ev){if(!drag||ev.pointerId!==drag.id)return;const d=drag;drag=null;
  try{d.e.releasePointerCapture(ev.pointerId);}catch(_){}
  if(!d.on)return;dragEnd=Date.now();d.e.classList.remove('dragging');
  const y=ev.clientY-d.r.top,onTable=y<handY-CH*.15;
  if(onTable&&g&&g.hands[0].indexOf(d.c)>=0&&canUse(d.c,true)){
    if(g.def===0){const ti=dropTarget(ev);if(ti>=0&&g.canDefend(0,d.c,ti)&&g.toMove()===0&&!botThinking){pending=null;target=-1;return myDo({t:'defend',c:d.c,i:ti});}
      if(ti>=0&&NET&&RU.cheat&&!g.table[ti].d&&g.toMove()===0&&!g.hands[0].some(x=>g.canTransfer(0,x)&&x===d.c)&&!g.table.some((x,k)=>g.canDefend(0,d.c,k))){pending=null;target=-1;return myDo({t:'cd',c:d.c,i:ti});}}
    onCard(d.c);if(g&&g.hands[0].indexOf(d.c)>=0)layout();}
  else if(g)layout();}
addEventListener('pointerup',dragFinish);addEventListener('pointercancel',dragFinish);

/* ---------- turns ---------- */
let bubT={};
function say(p,t,ok){if(ok===false||!t||p===0)return;const seat=$('seat'+p);if(!seat)return;const b=seat.querySelector('.bubble');
  // only one speech bubble at a time, so neighbours' lines never overlap
  document.querySelectorAll('.seat .bubble').forEach(o=>{if(o!==b)o.classList.add('off');});b.textContent=t;b.classList.remove('off');clearTimeout(bubT[p]);bubT[p]=setTimeout(()=>b.classList.add('off'),2300);}
function talk(evs){
  for(const e of evs){
    if(e.t==='attack'||e.t==='defend'||e.t==='transfer'||e.t==='show')flick();
    if(e.t==='show')flashCard(e.c,e.p);
    if(NET&&e.t==='accuse')netAccused(e);
    if(!trumpSeen&&(e.t==='show'||(e.t==='defend'&&e.c.s===g.trump&&g.table[e.i]&&g.table[e.i].a.s!==g.trump))){trumpSeen=true;gToast('Козырь открылся: '+SUIT_NAME_RU[g.trump]);}
    if(e.t==='draw'&&e.p===0&&chestCard&&e.c===chestCard&&!track.chest){track.chest=true;setTimeout(()=>{gToast('Клад! +'+CHEST_COINS+' монет в конце партии');coinSnd();},900);}
    if(e.p>0){const id=seatChar[e.p];
      if(e.t==='attack')say(e.p,charLine(id,g.table.length===1&&g.table[0].a===e.c?'lead':'toss'),Math.random()<.5);
      if(e.t==='take')say(e.p,charLine(id,'take'));
      if(e.t==='transfer'||e.t==='show')say(e.p,e.t==='show'?'Козырь!':charLine(id,'transfer'));
      if(e.t==='defend'&&!g.undefended().length&&g.table.length)say(e.p,charLine(id,'beat'),Math.random()<.4);}
  }
}
function afterAction(){
  const evs=g.events;g.events=[];talk(evs);
  if(!NET&&!save.live&&counts()){save.live={mode:g.mode,deck:g.deckSize,n:g.n};persist();}
  if(target>=0&&(!g.table[target]||g.table[target].d))target=-1;
  const end=evs.find(e=>e.t==='bito'||e.t==='took');if(end)myRun=false;
  if(RU.cheat){const ch=cheatSeen>=0?cheatSeen:(evs.find(e=>e.cheat)||{}).p;if(end&&ch!=null&&ch>=0&&!evs.some(e=>e.t==='accuse')){if(ch===0)gToast('Обман сошёл с рук!');else{track.missed++;gToast(`${CHR(seatChar[ch]).short} сжульничал, а вы не заметили!`);}}cheatSeen=end?-1:g.cheater();}
  if(!end){layout();return proceed();}
  const outs=evs.filter(e=>e.t==='out').map(e=>e.p);if(evs.some(e=>e.t==='over'))track.lastOuts=outs;
  if(fastFwd){masked=[];ghost=null;layout();return proceed();}
  anim=true;ghost=end.pairs;masked=evs.filter(e=>e.t==='draw').map(e=>e.c);layout();updateControls();
  const my=gen;
  wait(end.t==='took'?700:800,()=>{if(my!==gen)return;
    ghost=null;layout();
    if(end.t==='took'){slap();if(end.p===0&&end.att>0)say(end.att,charLine(seatChar[end.att],'playerTook'),Math.random()<.5);}
    else{swish();if(end.att>0)say(end.att,charLine(seatChar[end.att],'bito'),Math.random()<.5);}
    for(const p of outs){if(p>0)say(p,charLine(seatChar[p],'out'));else chime(true);}
    wait(600,()=>{if(my===gen)reveal(Math.max(110,190-g.n*12),()=>{anim=false;proceed();});});
  });
}
function proceed(){
  if(!g)return;if(!trumpSeen&&!g.deck.length){trumpSeen=true;gToast('Колода кончилась. Козырь: '+SUIT_NAME_RU[g.trump]);}
  if(chestCard&&!track.chest&&g.hands[0].includes(chestCard)){track.chest=true;gToast('Клад! +'+CHEST_COINS+' монет в конце партии');}
  stopTimer();layout();
  if(g.over){setActs([]);$('status').textContent='';$('skipOut').hidden=true;const my=gen;setTimeout(()=>{if(my===gen)showOver();},fastFwd?50:600);return;}
  if(paused){updateControls();return;}
  if(NET){botThinking=false;updateControls();netPump();return;}
  const tm=g.toMove();
  if(tm!==0){botThinking=true;updateControls();clearTimeout(botT);
    const fast=!g.active(0),more=myRun&&g.hands[0].some(c=>g.canAttack(0,c));
    const think=fastFwd?0:(fast?320:(560+Math.random()*420+(g.deck.length===0?220:0)+(more?900:0)))*SP();
    const gg=g;botT=setTimeout(()=>botAct(gg,tm),think);
  }else{botThinking=false;updateControls();}
}
function extraToss(p,P){const top=g.ranks.length-1;
  const c=g.hands[p].filter(c=>c.r!=='J'&&!g.isTrump(c)&&g.canAttack(p,c)&&g.rk(c)*8/top<=P.tossMax+1).sort((a,b)=>g.rk(a)-g.rk(b))[0];return c||null;}
function botAct(gg,p){
  botThinking=false;if(gg!==g||paused||!g)return;myRun=false;if(g.over||g.toMove()!==p)return proceed();
  const P=charPersona(seatChar[p]);const m=aiMove(g,p,P);
  if(tryCheat(p,m,P)){afterAction();return;}
  if(!m||!g.apply(p,m)){const L=g.legal(p);if(L.length)g.apply(p,L.find(x=>x.t==='take'||x.t==='done')||L[0]);}
  // a lead or a throw-in may come with a second card right away
  if(!fastFwd&&m&&m.t==='attack'&&!g.over&&Math.random()<(P.multi||0)){const c2=extraToss(p,P);
    if(c2){afterAction();anim=true;extraPending=true;botT=setTimeout(()=>{anim=false;extraPending=false;if(gg!==g||g.over||!g.canAttack(p,c2))return proceed();g.attack(p,c2);afterAction();},380*SP());return;}}
  afterAction();
}
$('skipOut').onclick=()=>{if(!g||g.active(0))return;fastFwd=true;$('skipOut').hidden=true;clearTimeout(botT);
  let guard=0;while(!g.over&&guard<5000){const p=g.toMove();const m=aiMove(g,p,charPersona(seatChar[p]),null,{fast:true});if(!m||!g.apply(p,m)){const L=g.legal(p);g.apply(p,L.find(x=>x.t==='take'||x.t==='done')||L[0]);}guard++;}
  const evs=g.events;g.events=[];const outs=evs.filter(e=>e.t==='out').map(e=>e.p);track.lastOuts=outs;masked=[];ghost=null;anim=false;proceed();};

/* ---------- results ---------- */
function showOver(){
  const n=g.n,fool=g.fool,team=!!g.teams,win=team?g.loserTeam!==g.teams[0]:fool!==0&&!(n===2&&fool===-1),draw=fool===-1;
  const r={win,firstOut:g.out[0]===0,takes:track.takes,transfers:track.transfers,bouts:g.bouts,
    pogGiven:g.pogony>0&&fool>0&&track.lastOuts.includes(0)&&(g.lastPlayed[0]||[]).some(c=>c.r==='6'),pogGot:g.pogony>0&&fool===0};
  // statistics
  save.live=null;
  const s=save.st;s.games++;if(win)s.wins++;else if(fool===0)s.losses++;else s.draws++;
  if(win){s.streak++;s.bestStreak=Math.max(s.bestStreak,s.streak);}else if(fool===0)s.streak=0;
  if(r.pogGiven)s.pogGiven++;if(r.pogGot)s.pogGot++;if(win&&r.takes===0)s.noTakeWins++;if(r.firstOut)s.firstOuts++;
  if(win&&n>=4)s.bigWins++;if(win&&n>=6)s.sixWins++;if(win&&g.deckSize===54)s.win54++;
  const bm=s.byMode[g.mode],bd=s.byDeck[g.deckSize]||(s.byDeck[g.deckSize]={g:0,w:0}),bp=s.byPlayers[n]||(s.byPlayers[n]={g:0,w:0});bm.g++;bd.g++;bp.g++;if(win){bm.w++;bd.w++;bp.w++;}
  // rewards
  const rw=[];let coins=0,starsShow=null;
  if(cfg.kind==='camp'){const L=LOCS[cfg.li],st=L.stages[cfg.si],key=stageKey(L.id,cfg.si),prev=stageRec(L.id,cfg.si);
    const got=st.goals.map(k=>goalMet(k,r)?1:0),stars=prev.stars.map((v,i)=>v||got[i]),newStars=stars.reduce((a,b)=>a+b,0)-prev.stars.reduce((a,b)=>a+b,0);
    if(win)coins+=stageReward(cfg.li,cfg.si,prev);coins+=newStars*10;
    save.camp[key]={won:prev.won||win,stars};starsShow=got;
    if(newStars>0)rw.push('★ +'+newStars);
    if(win&&!prev.won){if(L.id==='palace'&&cfg.si===2&&!save.owned.includes('palaty')){save.owned.push('palaty');rw.push('Стол «Царские палаты»');}
      if(L.id==='palace'&&cfg.si===3&&!save.owned.includes('tsar')){save.owned.push('tsar');rw.push('Рубашка «Царская»');}}
    if(starsTotal()>=STARS_MAX&&!save.owned.includes('gold')){save.owned.push('gold');rw.push('Колода «Золотая»');}
  }else if(NET){const o=netReward(win);coins+=o.coins;rw.push(...o.rw);}
  else if(win)coins+=quickReward(n-1,cfg.level)+(r.pogGiven?10:0);
  if(track.chest){coins+=CHEST_COINS;rw.push('Клад +'+CHEST_COINS);}
  if(track.caught){coins+=track.caught*10;rw.push('Пойман шулер ×'+track.caught+': +'+track.caught*10);}
  if(cfg.kind==='daily'){const got=cfg.goals.map(k=>goalMet(k,r)?1:0);starsShow=got;
    if(got.every(Boolean)&&!dailyDone()){save.daily={day:dayKey(),done:true};coins+=DAILY_REWARD;rw.push('Задание дня выполнено');
      s.dailyCount=(s.dailyCount||0)+1;if(s.dailyCount>=7&&!save.owned.includes('morozko')){save.owned.push('morozko');rw.push('Стол «Морозко»');}}
    else if(!dailyDone())rw.push('Задание дня не выполнено — попробуйте ещё');}
  else if(draw)coins+=5;
  if(coins&&win&&save.iap&&save.iap.boyar){coins*=2;rw.push('Боярский пакет: монеты ×2');}
  if(coins){addCoins(coins);rw.unshift('+'+coins+' монет');}
  lastWin=win?coins:0;
  persist();
  // texts
  let t,m;const foolName=fool>0?CHR(seatChar[fool]).name:'';
  if(team){const mateId=seatChar[2];t=win?'Ваша пара победила!':'Ваша пара проиграла';m=win?`В дураках — ${foolName}. ${ql(mateId,'win')}`:fool===0?'Карты остались у вас.':`Последним с картами остался напарник. ${ql(mateId,'lose')}`;}
  else if(n===2){if(draw){t='Ничья';m='Оба вышли разом. '+charLine(seatChar[1],'draw');}
    else if(win){t='Победа!';m=`${foolName} остаётся в дураках. ${ql(seatChar[1],'lose')}`;}
    else{t='Вы — дурак!';m=`${ql(seatChar[1],'win')}`;}}
  else{if(fool===0){t='Вы — дурак!';m=`Все вышли, а карты остались у вас. ${ql(seatChar[g.out[g.out.length-1]],'win')}`;}
    else if(draw){t='Без дурака!';m='Последние двое вышли одновременно.';}
    else{t=r.firstOut?'Вы вышли первым!':'Вы не дурак!';m=`В дураках — ${foolName}. ${ql(seatChar[fool],'lose')}`;}}
  win?chime(true):fool===0?chime(false):chime(true);
  // pogony picture
  const fig=$('pogFig');fig.hidden=true;
  if(!team&&g.pogony>0&&fool>=0&&(r.pogGiven||r.pogGot||n===2)){
    const outs=track.lastOuts.length?track.lastOuts:[1-fool];const sixes=outs.flatMap(p=>(g.lastPlayed[p]||[]).filter(c=>c.r==='6')).slice(0,2);
    if(sixes.length){const eps=fig.querySelectorAll('.ep');eps.forEach((e,i)=>{e.classList.remove('show');e.innerHTML=sixes[i]?faceSVG(sixes[i]):'';e.hidden=!sixes[i];});
      $('pogHead').innerHTML=portrait(seatChar[fool]);fig.hidden=false;
      requestAnimationFrame(()=>eps.forEach((e,i)=>{if(sixes[i]){e.classList.add('show');setTimeout(slap,i?650:300);}}));
      t=fool===0?'Погоны!':'Погоны: '+foolName+'!';}}
  $('overT').textContent=t;$('overP').textContent=m;
  const ob=$('overBadge');ob.hidden=true;
  if(cfg.kind==='camp'&&win){const L=LOCS[cfg.li],last=cfg.si===L.stages.length-1;ob.hidden=false;
    ob.textContent=last?`Место «${L.name}» пройдено!`:`Этап ${cfg.si+1} из ${L.stages.length} пройден`;ob.classList.toggle('big',last);}
  // stars
  const os=$('overStars');if(starsShow){os.hidden=false;os.innerHTML=starsShow.map((v,i)=>`<span class="${v?'on':''}" style="animation-delay:${.2+i*.25}s" title="${GOALS[cfg.goals[i]].t}">★</span>`).join('');}else os.hidden=true;
  // places for bigger tables
  const pl=$('places');if(n>2){const order=g.out.slice();if(fool>=0)order.push(fool);
    pl.innerHTML=order.map((p,i)=>`<div class="${p===0?'me':''}"><span>${i+1}. ${p===0?'Вы':CHR(seatChar[p]).name}</span><span>${p===fool?'дурак':i===0?'первым':''}</span></div>`).join('');pl.hidden=false;}else pl.hidden=true;
  $('overRw').innerHTML=rw.map(x=>`<span>${x.startsWith('+')&&x.includes('монет')?'<span class="coin">₽</span>':''}${x}</span>`).join('');
  if(typeof moneyOver==='function')moneyOver(win);
  // buttons
  const main=$('overMain'),alt=$('overAlt');
  if(cfg.kind==='camp'){const L=LOCS[cfg.li];let next=null;
    if(win){if(cfg.si+1<L.stages.length)next=[cfg.li,cfg.si+1];else if(cfg.li+1<LOCS.length)next=[cfg.li+1,0];}
    const placeDone=win&&cfg.si===L.stages.length-1;
    if(placeDone){main.textContent=next?'Дальше':'К карте';main.onclick=()=>{modal('over',false);clearAll();placeFinished(cfg.li,next);};}
    else if(next){main.textContent='Следующий соперник';main.onclick=()=>{modal('over',false);clearAll();show('camp');openStage(next[0],next[1]);};}
    else{main.textContent='Ещё раз';main.onclick=()=>{modal('over',false);startGame(cfg);};}
    alt.textContent='К карте';alt.onclick=()=>{modal('over',false);clearAll();show('camp');};}
  else if(NET)netOverButtons(main,alt);
  else{main.textContent='Ещё партию';main.onclick=()=>{modal('over',false);startGame(cfg);};alt.textContent='Меню';alt.onclick=()=>{modal('over',false);clearAll();show('home');};}
  modal('over',true);main.focus();layout();
  setTimeout(checkAch,900);
}

// a whole place of the journey is behind: a moment of its own, then the map with the new place lit up
function placeFinished(li,next){const L=LOCS[li],got=L.stages.reduce((a,s,si)=>a+stageRec(L.id,si).stars.reduce((x,y)=>x+y,0),0);
  $('pdT').textContent='Место пройдено!';
  $('pdStars').innerHTML=`«${L.name}» · <span class="on">★</span> ${got} из 12`;
  const N=next&&LOCS[next[0]];
  $('pdNext').innerHTML=N?`Открыто новое место:<b>${N.name}</b><span>${N.rule}</span>`:'<b>Весь Царский путь пройден!</b><span>Вы — лучший игрок царства.</span>';
  $('pdGo').textContent=N?'Отправиться':'К карте';
  $('pdGo').onclick=()=>{modal('placeDone',false);show('camp');if(N){const el=$('locs').children[next[0]];if(el){el.scrollIntoView({block:'center'});el.classList.add('fresh');setTimeout(()=>el.classList.remove('fresh'),2600);}}};
  chime(true);modal('placeDone',true);$('pdGo').focus();}
window.__durak={applySkin,placeFinished,get net(){return net;},backSVG,faceSVG,music,portrait,get g(){return g;},get busy(){return anim||botThinking;},showOver,startGame,get save(){return save;}};
// a game you walk away from after it has begun counts as a loss: otherwise "start again" would wipe every defeat.
// Closing the page mid-game counts the same, the next time the game opens.
function counts(){return !!g&&!g.over&&g.active(0)&&(g.bouts>0||g.table.length>0);}
function recordLoss(L){const s=save.st;s.games++;s.losses++;s.quits=(s.quits||0)+1;s.streak=0;
  const bm=s.byMode[L.mode],bd=s.byDeck[L.deck]||(s.byDeck[L.deck]={g:0,w:0}),bp=s.byPlayers[L.n]||(s.byPlayers[L.n]={g:0,w:0});if(bm)bm.g++;bd.g++;bp.g++;}
function forfeit(){if(counts()&&save.live)recordLoss(save.live);save.live=null;persist();}
if(save.live){recordLoss(save.live);save.live=null;persist();}
applySpeed();show('home');

/* ---------- friends' table: screens, connection and following the server ---------- */
// The server address is set by the page (index.html) once the cloud part exists.
const NET_API=window.__NET_API||'',NET_WS=window.__NET_WS||'',NET_SHARE=window.__NET_SHARE||'https://ttgms.github.io/durak/';
const PHRASES=['Привет!','Ходи!','Ну ты даёшь!','Эх…','Хорошая игра!','Быстрее!','Ха-ха!','Спасибо!','Сейчас отыграюсь','Ой, всё','👍','😂','😮','😡','🎉','🙈'];
const net={pend:[],code:'',tok:'',room:null,m:null,q:[],have:0,cs:0,wait:false,ws:null,wsOk:false,rid:0,cb:{},skew:0,loop:0,busy:false,game:0,lastIn:0,lastPoll:0,lastApply:0,pumpT:0};
const esc=s=>String(s==null?'':s).replace(/[&<>"']/g,ch=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[ch]));
function netWait(){return net.wait;}
const AVA_COL=['#c0392b','#2e6fb7','#2f8f5b','#8e44ad','#d68910','#16a085'];
function avatarSVG(nm,i){return `<svg viewBox="0 0 40 40" aria-hidden="true"><circle cx="20" cy="20" r="17" fill="${AVA_COL[i%6]}"/><text x="20" y="26.5" text-anchor="middle" font-family="Rubik,sans-serif" font-weight="700" font-size="18" fill="#fff">${esc((nm||'?')[0].toUpperCase())}</text></svg>`;}
// people at the table look like characters to the rest of the game: a name and a picture, no lines
function netChar(id){const i=+String(id).slice(1),s=net.room&&net.room.seats[i],nm=s&&s.nm||'Игрок';
  return {name:nm+(s&&s.away?' (нет связи)':''),short:nm,pic:avatarSVG(nm,i),lines:{}};}
function netSeatChars(){const r=net.room,n=r.seats.length,me=r.me;
  return [...Array(n)].map((_,q)=>{if(q===0)return 'you';const s=(q+me)%n,x=r.seats[s];return x.k==='b'?x.ch:'h'+s;});}

/* ---------- talking to the server ---------- */
// text/plain keeps it a "simple" request: no extra CORS round trip before every move
function netHttp(body){return fetch(NET_API,{method:'POST',headers:{'Content-Type':'text/plain'},body:JSON.stringify(body)}).then(r=>r.json());}
function netReq(op,data){
  const body=Object.assign({op,code:net.code,tok:net.tok,since:net.m?net.have:-1,cs:net.cs},data||{});
  const since=body.since;
  const done=v=>{v=v||{err:'net'};v._since=since;return v;};
  if(op!=='create'&&op!=='join'&&net.ws&&net.wsOk){const rid=++net.rid;body.rid=rid;
    return new Promise(ok=>{net.cb[rid]=v=>ok(done(v));try{net.ws.send(JSON.stringify(body));}catch(e){}
      setTimeout(()=>{if(net.cb[rid]){delete net.cb[rid];netHttp(body).then(v=>ok(done(v)),()=>ok(done(null)));}},5000);});}
  return netHttp(body).then(done,()=>done(null));}
function netCall(op,data){return netReq(op,data).then(v=>{netOn(v,v._since);return v;});}
// everything the server says comes through here
function netOn(v,since){
  if(!v)return;net.lastIn=Date.now();if(v.now)net.skew=v.now-Date.now();
  if(v.err){
    if(v.err==='no room'||v.err==='not seated'){netGone(v.err==='no room'?'Стол закрыт или устарел.':'Вас нет за этим столом.');return;}
    if(v.err==='not your turn'||v.err==='illegal'){gToast('Ход не прошёл');if(v.room)netResync();}
    if(v.err==='net'&&!v.room)return;}
  if(!v.room)return;
  net.room=v.room;
  if(v.chat)for(const c of v.chat)if(c.i>net.cs){net.cs=c.i;netSay(c);}
  if(v.room.st==='lobby'||v.room.st==='closed'){if(net.m){NET=false;net.m=null;clearAll();}if(v.room.st==='closed'){netGone('Хозяин закрыл стол.');return;}renderLobby();return;}
  if(v.snap){netStartGame(v.snap);return;}
  if(!net.m||v.room.game!==net.game){netResync();return;}
  if(v.log){const from=v.push?v.from:since;
    if(from==null||from<0||from>net.have){netResync();return;}
    for(let k=net.have-from;k<v.log.length;k++){net.q.push(v.log[k]);net.have++;}
    netPump();}
  refreshNetSeats();}
let resyncing=false;
function netResync(){if(resyncing)return;resyncing=true;
  netReq('poll',{since:-1}).then(v=>{resyncing=false;if(v&&v.snap&&v.room){net.room=v.room;netStartGame(v.snap,true);}else netOn(v,-1);});}

/* ---------- connection upkeep: WebSocket if there is one, otherwise asking every second ---------- */
function netConnect(){
  netStopLoop();
  if(NET_WS&&'WebSocket' in window)netOpenWs();
  net.loop=setInterval(netTick,500);}
function netStopLoop(){clearInterval(net.loop);net.loop=0;if(net.ws){try{net.ws.onclose=null;net.ws.close();}catch(e){}net.ws=null;net.wsOk=false;}}
function netOpenWs(){
  let ws;try{ws=new WebSocket(NET_WS);}catch(e){return;}net.ws=ws;
  ws.onopen=()=>{net.wsOk=true;netCall('poll');};
  ws.onmessage=ev=>{let v;try{v=JSON.parse(ev.data);}catch(e){return;}if(!v||(!v.room&&!v.err&&!v.rid))return;
    if(v.rid&&net.cb[v.rid]){const f=net.cb[v.rid];delete net.cb[v.rid];f(v);return;}
    if(v.push)netOn(v,v.from);};
  ws.onclose=()=>{net.wsOk=false;net.ws=null;if(net.code)setTimeout(()=>{if(net.code&&!net.ws)netOpenWs();},2000);};}
function netTick(){
  if(!net.code)return;const now=Date.now();
  const r=net.room,mine=net.m&&g&&!g.over&&g.toMove()===0;
  // ask the server: always without WebSocket, as a keep-alive with it, and when something is overdue
  const overdue=r&&r.dl&&now+net.skew>r.dl+1500;
  const every=!net.wsOk?(r&&r.st==='lobby'?1500:1000):20000;
  if(!net.busy&&(now-net.lastPoll>every||(overdue&&now-net.lastPoll>2500)||(net.wsOk&&r&&r.st==='play'&&!mine&&now-net.lastIn>6000&&now-net.lastPoll>3000))){
    net.busy=true;net.lastPoll=now;netCall('poll').then(()=>{net.busy=false;},()=>{net.busy=false;});}
  netTimer();}

/* ---------- the game: follow the server's log on our copy of the table ---------- */
function netStartGame(snap,quiet){
  NET=true;net.game=net.room.game;net.q=[];net.wait=false;
  net.m=new Mirror(snap,net.room.me,{reveal:netReveal});net.have=snap.logLen;net.pend=[];
  const o=net.room.opts,fresh=snap.logLen===0&&!snap.over;
  startGame({kind:'online',mirror:net.m,fresh:fresh&&!quiet,mode:o.mode,deck:o.deck,level:o.level,rules:Object.assign({},o.rules,{timer:false}),skin:save.tableSkin,goals:null,opps:[]});
  $('chatBtn').hidden=false;}
// a stand-in card turned out to be a real one: its picture changes, its place in the game stays
function netReveal(old,obj){const e=els[old];if(!e)return;delete els[old];els[obj.id]=e;
  e.querySelector('.f').innerHTML=faceSVG(obj);e.setAttribute('aria-label',obj.r==='J'?(obj.s==='r'?'красный джокер':'чёрный джокер'):obj.r+' '+SUIT_NAME[obj.s]);}
function netPump(){
  clearTimeout(net.pumpT);
  if(!NET||!g||anim||!net.q.length||!net.m)return;
  // moves that arrive together are still shown one after another
  const gap=net.lastApply+380*SP()-Date.now();if(gap>0){net.pumpT=setTimeout(netPump,gap);return;}
  const e=net.q.shift();
  // the confirmation of a move I already played
  if(net.pend.length){const p=net.pend[0];
    if(net.m.R(e.p)===0&&e.t===p.t&&(e.c||undefined)===p.c){net.pend.shift();const n0=g.events.length;
      if(!net.m.echo(e,p)){netResync();return;}
      if(g.events.length>n0||g.over){net.lastApply=Date.now();afterAction();}else netPump();return;}
    netResync();return;}
  net.lastApply=Date.now();
  if(!net.m.apply(e)){netResync();return;}
  if(net.m.R(e.p)!==0&&e.t==='take')botThinking=false;
  afterAction();}
function netMove(m){
  if(net.wait||!net.m)return;const wire=net.m.wire(m);
  // most moves go down at once and the server confirms them a moment later; a call-out waits for the server
  if(m.t!=='acc'&&!net.q.length&&!resyncing){const p=net.m.local(m);if(!p){shake(m.c||g.hands[0][0]);return;}
    net.pend.push(p);net.lastApply=Date.now();
    netReq('act',{m:wire}).then(v=>{if(v.err){net.pend=[];if(v.err==='net')gToast('Нет связи — ход не дошёл');netResync();return;}netOn(v,v._since);});
    afterAction();return;}
  net.wait=true;markPlayable();
  netReq('act',{m:wire}).then(v=>{net.wait=false;netOn(v,v._since);if(v.err==='net'){gToast('Нет связи — ход не отправлен');markPlayable();}});}
function netAccused(e){const w=q=>q===0?'вас':CHR(seatChar[q]).short;
  if(e.p===0){if(e.caught){track.caught++;gToast(`Поймал! ${CHR(seatChar[e.loser]).short} забирает карты`);coinSnd();}else gToast('Обмана не было — карты забираете вы');}
  else if(e.caught)gToast(e.loser===0?`${CHR(seatChar[e.p]).short} поймал вас на обмане!`:`${CHR(seatChar[e.p]).short} поймал ${w(e.loser)}!`);
  else gToast(`${CHR(seatChar[e.p]).short} ошибся — забирает карты`);}
function netTimer(){const el=$('tmr');
  if(!NET||!g||g.over||anim||!net.room||!net.room.dl||g.toMove()!==0||!g.active(0)){if(NET)el.hidden=true;return;}
  const left=Math.ceil((net.room.dl-(Date.now()+net.skew))/1000);
  if(left>net.room.opts.timer){el.hidden=true;return;}
  el.hidden=false;const v=Math.max(0,left);if(el.textContent!==String(v)){el.textContent=v;if(v<=3&&v>0)tones([[880,0,.06]],'sine',.04);}el.classList.toggle('low',v<=5);}
function refreshNetSeats(){if(!NET||!g||!net.room)return;
  for(let q=1;q<g.n;q++){const el=$('seat'+q);if(!el)continue;const s=net.room.seats[(q+net.room.me)%g.n];el.classList.toggle('away',!!(s&&s.k==='h'&&s.away));}}
function netSay(c){const q=net.room?(c.p-net.room.me+net.room.seats.length)%net.room.seats.length:-1,t=PHRASES[c.k]||'';
  if(!t)return;if(NET&&g){if(q===0)gToast(t);else say(q,t);}
  else{const el=$('lChat');if(el){const s=net.room.seats[c.p];el.textContent=(s&&s.nm?s.nm:'Игрок')+': '+t;el.classList.remove('on');void el.offsetWidth;el.classList.add('on');}}}
function netReward(win){const o={coins:0,rw:[]};if(!win)return o;
  const people=net.room.seats.filter(x=>x.k==='h').length;
  if(people>=2){const d=dayKey();if(!save.netDay||save.netDay.d!==d)save.netDay={d,w:0};
    if(save.netDay.w<5){save.netDay.w++;o.coins+=30;}else o.rw.push('Монеты за победы над друзьями — до 5 раз в день');
    if(!save.owned.includes('skaz')){save.owned.push('skaz');o.rw.push('Колода «Сказочная»');}}
  else o.coins+=quickReward(g.n-1,net.room.opts.level);
  return o;}
function netOverButtons(main,alt){const host=net.room.host===net.room.me;
  if(host){main.textContent='Ещё партию';main.disabled=false;main.onclick=()=>{main.disabled=true;netCall('start');};}
  else{main.textContent='Ждём хозяина стола…';main.disabled=true;}
  alt.textContent='Выйти из-за стола';alt.onclick=()=>{modal('over',false);netLeave();};}
function netLeave(){if(NET&&counts())recordLoss({mode:g.mode,deck:g.deckSize,n:g.n});const code=net.code;if(code)netReq('leave');netStopLoop();
  NET=false;net.m=null;net.code='';net.room=null;net.q=[];save.net=Object.assign(save.net||{},{code:'',tok:''});persist();
  $('chatBtn').hidden=true;$('chatP').hidden=true;clearAll();modal('over',false);show('friends');}
function netGone(msg){netStopLoop();NET=false;net.m=null;net.code='';net.room=null;save.net=Object.assign(save.net||{},{code:'',tok:''});persist();
  $('chatBtn').hidden=true;$('chatP').hidden=true;clearAll();modal('over',false);modal('pause',false);show('friends');$('fMsg').textContent=msg;}

/* ---------- phrases ---------- */
$('chatP').innerHTML=PHRASES.map((t,k)=>`<button type="button" data-k="${k}">${t}</button>`).join('');
$('chatBtn').onclick=()=>{$('chatP').hidden=!$('chatP').hidden;};
$('chatP').querySelectorAll('button').forEach(b=>b.onclick=()=>{$('chatP').hidden=true;netCall('say',{k:+b.dataset.k});});
$('lChatBtn').onclick=()=>{$('lChatP').hidden=!$('lChatP').hidden;};
$('lChatP').innerHTML=PHRASES.map((t,k)=>`<button type="button" data-k="${k}">${t}</button>`).join('');
$('lChatP').querySelectorAll('button').forEach(b=>b.onclick=()=>{$('lChatP').hidden=true;netCall('say',{k:+b.dataset.k});});

/* ---------- screens: friends' menu and the table before the game ---------- */
if(!save.net)save.net={name:'',code:'',tok:''};
function renderFriends(){$('fName').value=save.net.name||'';
  const back=!!(save.net.code&&save.net.tok);$('fBack').hidden=!back;if(back)$('fBackCode').textContent=save.net.code;
  $('fOff').hidden=!!NET_API;$('fCreate').disabled=!NET_API;$('fJoin').disabled=!NET_API;}
function myName(){const v=$('fName').value.replace(/[<>&"'`\\]/g,'').trim().slice(0,14);save.net.name=v;persist();return v||'Игрок';}
function netEnter(v){if(!v||v.err||!v.room){$('fMsg').textContent=v&&v.err==='full'?'За столом нет свободных мест.':v&&v.err==='started'?'Игра за этим столом уже идёт.':v&&(v.err==='no room'||v.err==='bad code')?'Стол с таким кодом не найден.':'Не получилось связаться с сервером. Попробуйте ещё раз.';return;}
  net.code=v.room.code;if(v.tok)net.tok=v.tok;net.room=v.room;net.cs=0;net.m=null;net.have=0;
  save.net=Object.assign(save.net,{code:net.code,tok:net.tok});persist();
  $('fMsg').textContent='';netConnect();netOn(v,-1);}
$('hFriends').onclick=()=>{audio();show('friends');};
$('fCreate').onclick=()=>{audio();$('fMsg').textContent='Создаём стол…';const q=save.quick;
  netReq('create',{name:myName(),opts:{deck:q.deck===52&&q.jokers?54:q.deck,n:Math.max(2,Math.min(q.players,4)),mode:q.mode,level:q.level==='hard'?'hard':q.level==='easy'?'easy':'medium',timer:30,rules:quickRules(q)}}).then(netEnter);};
$('fJoin').onclick=()=>{audio();const code=$('fCode').value.trim();if(!code){$('fCode').focus();return;}$('fMsg').textContent='Подключаемся…';
  netReq('join',{code,name:myName(),tok:save.net.code&&save.net.tok?save.net.tok:''}).then(netEnter);};
$('fCode').addEventListener('keydown',e=>{if(e.key==='Enter')$('fJoin').click();});
$('fBack').onclick=()=>{audio();$('fMsg').textContent='Подключаемся…';netReq('join',{code:save.net.code,name:myName(),tok:save.net.tok}).then(v=>{if(v&&v.err){save.net.code='';save.net.tok='';persist();renderFriends();}netEnter(v);});};
$('lLeave').onclick=()=>netLeave();
function shareLink(){return NET_SHARE+'?t='+encodeURIComponent(net.code);}
$('lShare').onclick=()=>{const url=shareLink(),text='Садись со мной за стол в «Дурака»! Код стола: '+net.code;
  if(navigator.share)navigator.share({title:'Дурак: Царский турнир',text,url}).catch(()=>{});else copyText(text+' '+url);};
$('lCopy').onclick=()=>copyText(shareLink());
function copyText(t){const ok=()=>{$('lCopy').textContent='Скопировано!';setTimeout(()=>$('lCopy').textContent='Скопировать ссылку',1600);};
  if(navigator.clipboard&&navigator.clipboard.writeText)navigator.clipboard.writeText(t).then(ok,()=>prompt('Ссылка на стол:',t));else prompt('Ссылка на стол:',t);}
const RULE_CHIPS=[['neighbors','Только соседи'],['show','Перевод показом'],['noLimit','Без лимита'],['teams','Пара на пару'],['cheat','Шулерство'],['open','Открытые карты'],['fog','Туман'],['dark','Тёмный козырь'],['chest','Клад']];
const RULE_NEED={neighbors:o=>o.n<3?'от 3 игроков':'',show:o=>o.mode!=='perevodnoy'?'в переводном':'',teams:o=>o.n!==4?'ровно 4 игрока':'',fog:o=>o.rules.open?'не с открытыми':''};
const LEVEL_NAME={easy:'лёгкие',medium:'средние',hard:'сильные'};
function cfgSend(ch){netCall('cfg',{ch});}
function renderLobby(){
  if($('lobby').hidden)show('lobby');
  const r=net.room,host=r.host===r.me,o=r.opts,maxN={24:4,36:5,52:6,54:6}[o.deck];
  $('lCode').textContent=r.code;
  const ppl=r.seats.filter(x=>x.k==='h').length,open=r.seats.filter(x=>x.k==='o').length;
  $('lSub').textContent=open?`Ждём друзей: свободно ${plural(open,'место','места','мест')}`:`За столом ${plural(ppl,'человек','человека','человек')}`;
  $('lSeats').innerHTML=r.seats.map((x,i)=>{
    const who=x.k==='h'?`<span class="pic">${avatarSVG(x.nm,i)}</span><b>${esc(x.nm)}</b>${i===r.me?'<em>вы</em>':''}${i===r.host?'<em>хозяин</em>':''}${x.away?'<em>нет связи</em>':''}`
      :x.k==='b'?`<span class="pic bot">🤖</span><b>Бот</b><em>${LEVEL_NAME[o.level]}</em>`:`<span class="pic free">+</span><b class="dim">Свободное место</b>`;
    const btn=host&&x.k!=='h'?`<button type="button" class="plain sm" data-s="${i}">${x.k==='o'?'Посадить бота':'Освободить'}</button>`:'';
    return `<div class="lseat">${who}${btn}</div>`;}).join('');
  $('lSeats').querySelectorAll('[data-s]').forEach(b=>b.onclick=()=>cfgSend({seat:+b.dataset.s}));
  const O=$('lOpts');
  if(host){
    O.innerHTML=`<div class="opt"><span class="lbl">Колода</span><div class="seg" id="loDeck"></div></div>
      <div class="opt"><span class="lbl">Мест за столом</span><div class="seg" id="loN"></div></div>
      <div class="opt"><span class="lbl">Правила</span><div class="seg" id="loMode"></div></div>
      <div class="opt"><span class="lbl">Боты на пустых местах</span><div class="seg" id="loLevel"></div></div>
      <div class="opt"><span class="lbl">Время на ход</span><div class="seg" id="loTimer"></div></div>
      <div class="opt"><span class="lbl">Особые правила</span><div class="seg chips" id="loRules"></div></div>`;
    segButtons($('loDeck'),[[24,'24'],[36,'36'],[52,'52'],[54,'54 с джокерами']],o.deck,v=>cfgSend({opts:{deck:v}}));
    segButtons($('loN'),[2,3,4,5,6].map(k=>[k,String(k),k>maxN||k<ppl]),o.n,v=>cfgSend({opts:{n:v}}));
    segButtons($('loMode'),[['podkidnoy','Подкидной'],['perevodnoy','Переводной']],o.mode,v=>cfgSend({opts:{mode:v}}));
    segButtons($('loLevel'),[['easy','Лёгкие'],['medium','Средние'],['hard','Сильные']],o.level,v=>cfgSend({opts:{level:v}}));
    segButtons($('loTimer'),[[15,'15 с'],[30,'30 с'],[60,'60 с']],o.timer,v=>cfgSend({opts:{timer:v}}));
    $('loRules').innerHTML=RULE_CHIPS.map(([k,t])=>{const need=RULE_NEED[k]?RULE_NEED[k](o):'';return `<button type="button" aria-pressed="${!!o.rules[k]}" ${need?'disabled':''} data-k="${k}">${t}${need?` <small>(${need})</small>`:''}</button>`;}).join('');
    $('loRules').querySelectorAll('button').forEach(b=>b.onclick=()=>{const rl=Object.assign({},o.rules);rl[b.dataset.k]=!rl[b.dataset.k];if(!rl[b.dataset.k])delete rl[b.dataset.k];cfgSend({opts:{rules:rl}});});
  }else{
    const rl=RULE_CHIPS.filter(([k])=>o.rules[k]).map(([,t])=>t);
    O.innerHTML=`<div class="panel lsum"><div><span>Колода</span><b>${o.deck===54?'54 с джокерами':o.deck}</b></div><div><span>Правила</span><b>${MODE_NAME[o.mode]}</b></div>
      <div><span>Время на ход</span><b>${o.timer} с</b></div><div><span>Боты</span><b>${LEVEL_NAME[o.level]}</b></div>${rl.length?`<div><span>Особые</span><b>${rl.join(', ')}</b></div>`:''}</div>`;}
  $('lStart').hidden=!host;$('lWait').textContent=host?(open?'Свободные места займут боты, если начать сейчас.':''):'Хозяин стола начнёт игру, когда все соберутся.';}
$('lStart').onclick=()=>{audio();netCall('start');};
// a link with ?t=CODE opens the friends' screen ready to join
(function(){try{const t=new URLSearchParams(location.search).get('t');if(t){$('fCode').value=t;show('friends');renderFriends();$('fMsg').textContent='Введите имя и нажмите «Войти».';}}catch(e){}})();

/* ---------- shop for real money and ads for rewards (only where the platform offers them: Pikabu) ---------- */
// window.__PF is set by the platform page before the game starts; the plain site has none, and all of this stays hidden.
const PF=window.__PF||null;
if(!save.iap)save.iap={};if(!save.iapDone)save.iapDone={};
const IAP=[
  {id:'boyar',name:'Боярский пакет',d:'Навсегда без рекламы, монеты за победы ×2 и рубашка «Боярская», которой больше нигде нет',big:true},
  {id:'noads',name:'Без рекламы',d:'Навсегда убирает рекламу между партиями. Реклама за награду остаётся по желанию'},
  {id:'starter',name:'Стартовый набор',d:'2 000 монет, рубашка «Городец» и колода «Русская»'},
  {id:'coins3000',name:'Мешок монет',d:'3 000 монет'},
  {id:'coins10000',name:'Царская казна',d:'10 000 монет — больше всего монет за рубль'}];
const COINS_OF={coins3000:3000,coins10000:10000};
function own(id){if(!save.owned.includes(id))save.owned.push(id);}
// what a product gives; permanent ones are given once and remembered
function grant(id,purchaseId){
  if(COINS_OF[id]){if(purchaseId&&save.iapDone[purchaseId])return false;if(purchaseId)save.iapDone[purchaseId]=1;addCoins(COINS_OF[id]);return true;}
  if(save.iap[id])return false;save.iap[id]=true;
  if(id==='starter'){addCoins(2000);own('gorodets');own('russ');}
  if(id==='boyar'){own('boyar');save.iap.noads=true;}
  if(id==='noads')save.iap.noads=true;
  persist();return true;}
const noAds=()=>!!(save.iap.noads||save.iap.boyar);
// ads pause the game's sound
function withAd(show){if(!PF)return Promise.resolve(null);const wasPaused=paused;paused=true;try{if(ac)ac.suspend();}catch(e){}
  const back=r=>{paused=wasPaused;try{if(ac&&!document.hidden)ac.resume();}catch(e){}return r;};
  return show().then(back,()=>back(null));}
function rewarded(){return withAd(()=>PF.rewarded()).then(r=>!!r);}
let rewardedOk=false;
function checkRewarded(){if(!PF)return;Promise.resolve(PF.canRewarded()).then(v=>{rewardedOk=!!v;refreshAdButtons();},()=>{});}

/* --- purchases made earlier (and coin packs paid for but not yet given) --- */
function applyOwned(){if(!PF||!PF.store)return;let changed=false;
  for(const id of PF.store.owned())if(!COINS_OF[id])changed=grant(id)||changed;
  for(const p of PF.store.pending()){if(grant(p.productId,p.purchaseId))changed=true;PF.store.consume(p.purchaseId);}
  if(changed){refreshCoins();if(!$('shop').hidden)renderShop();}}
if(PF){applyOwned();addEventListener('pf-store',()=>{applyOwned();if(!$('shop').hidden)renderShop();});}

/* --- the «Казна» tab in the shop --- */
const AD_COINS=60,AD_COINS_DAY=5;
function adCoinsLeft(){const d=dayKey();if(!save.adCoins||save.adCoins.d!==d)save.adCoins={d,n:0};return AD_COINS_DAY-save.adCoins.n;}
if(PF){$('tbIap').hidden=false;$('tbIap').onclick=()=>{shopTab='iap';renderShop();};
  // the treasury is also on the main menu, so nobody has to hunt for it
  $('hIap').onclick=()=>{audio();shopTab='iap';show('shop');};}
// the bar on the main menu sells one thing at a time, the most tempting one this player does not have yet,
// and quietly turns to the next offer every few seconds
const BAR_OFFERS=[
  {id:'noads',ic:'🚫',t:'Играйте без рекламы',sub:p=>`Навсегда — всего за ${p} ₽`,skip:()=>noAds()},
  {id:'starter',ic:'🎒',t:'Стартовый набор',sub:p=>`2 000 монет, рубашка и колода — ${p} ₽`,skip:()=>!!save.iap.starter},
  {id:'boyar',ic:'👑',t:'Боярский пакет',sub:p=>`Без рекламы, монеты ×2 и особая рубашка — ${p} ₽`,skip:()=>!!save.iap.boyar},
  {id:'coins10000',ic:'💰',t:'Царская казна',sub:p=>`10 000 монет — ${p} ₽`,skip:()=>false}];
let barI=0,barT=0;
function renderIapBar(){const b=$('hIap');if(!PF||!PF.store){b.hidden=true;return;}const prod=PF.store.products();
  const list=BAR_OFFERS.filter(o=>!o.skip()&&prod.some(x=>x.id===o.id));b.hidden=!list.length;if(!list.length)return;
  const o=list[barI%list.length],p=prod.find(x=>x.id===o.id).price;
  b.querySelector('.ic').textContent=o.ic;b.querySelector('b').textContent=o.t;$('hIapSub').textContent=o.sub(p);
  b.querySelector('.go').textContent='Смотреть ›';
  clearTimeout(barT);if(list.length>1)barT=setTimeout(()=>{if($('home').hidden){barT=0;return;}b.classList.add('flip');
    setTimeout(()=>{barI++;renderIapBar();b.classList.remove('flip');},250);},6000);}
if(PF){addEventListener('pf-store',renderIapBar);renderIapBar();}
const renderShop0=renderShop;
renderShop=function(){
  $('tbIap').setAttribute('aria-selected',String(shopTab==='iap'));
  if(shopTab!=='iap'){renderShop0();return;}
  ['tbBacks','tbFaces','tbTables'].forEach(id=>$(id).setAttribute('aria-selected','false'));
  const st=PF&&PF.store,prod=st?st.products():[];
  const price=id=>{const p=prod.find(x=>x.id===id);return p?p.price:null;};
  let h='';
  if(rewardedOk||adCoinsLeft()>0){const left=adCoinsLeft();
    h+=`<div class="panel item iap ad"><div class="iapic">🎁</div><h4>Монеты за рекламу</h4><div class="d">+${AD_COINS} монет за короткий ролик</div><div class="how">Осталось сегодня: ${left} из ${AD_COINS_DAY}</div>
      <button class="gold" id="adCoins" type="button" ${left<=0||!rewardedOk?'disabled':''}>Смотреть</button></div>`;}
  for(const it of IAP){const pr=price(it.id),have=!COINS_OF[it.id]&&save.iap[it.id];
    const bought=have||(it.id==='noads'&&save.iap.boyar);
    h+=`<div class="panel item iap${it.big?' big':''}"><div class="iapic">${it.id==='boyar'?backSVG('boyar'):it.id==='noads'?'🚫':it.id==='starter'?'🎒':'💰'}</div><h4>${it.name}</h4><div class="d">${it.d}</div>
      ${bought?'<div class="sel">✓ Куплено</div>':pr==null?'<button class="gold" disabled type="button">Недоступно</button>':`<button class="gold" data-iap="${it.id}" type="button">${pr} ₽</button>`}</div>`;}
  $('shopGrid').innerHTML=h;
  const ac0=$('adCoins');if(ac0)ac0.onclick=()=>{if(adCoinsLeft()<=0)return;ac0.disabled=true;rewarded().then(ok=>{if(ok){save.adCoins.n++;addCoins(AD_COINS);coinSnd();}checkRewarded();renderShop();});};
  $('shopGrid').querySelectorAll('[data-iap]').forEach(b=>b.onclick=()=>{const id=b.dataset.iap;b.disabled=true;b.textContent='Оплата…';
    withAd(()=>st.buy(id)).then(r=>{
      if(r&&r.ok){grant(id,r.purchaseId);if(COINS_OF[id]&&r.purchaseId)st.consume(r.purchaseId);coinSnd();checkAch();
        if(id==='boyar'||id==='starter')toast('Спасибо за покупку!',IAP.find(x=>x.id===id).name);}
      else if(r&&r.reason==='NON_CONSUMABLE_ALREADY_OWNED')grant(id);
      renderShop();refreshCoins();});});
  refreshCoins();};

/* --- rewards for watching: double the win, double the daily gift, swap the daily task, a hint --- */
function moneyOver(win){
  const box=$('overRw');if(!PF||!win||lastWin<=0||!rewardedOk)return;
  box.insertAdjacentHTML('beforeend',`<button id="adDouble" class="plain adbtn" type="button">📺 Удвоить: +${lastWin} за рекламу</button>`);
  $('adDouble').onclick=()=>{const b=$('adDouble');b.disabled=true;rewarded().then(ok=>{if(ok){addCoins(lastWin);coinSnd();b.textContent='✓ Монеты удвоены';}else b.disabled=false;checkRewarded();});};}
if(PF){
  $('giftAd').onclick=()=>{const b=$('giftAd');b.disabled=true;rewarded().then(ok=>{
    if(ok){const amount=+$('giftTake').dataset.amount||0;$('giftTake').click();addCoins(amount);toast('Подарок удвоен','+'+amount+' монет');}else b.disabled=false;checkRewarded();});};
  $('dailyAlt').onclick=e=>{e.stopPropagation();if(dailyDone())return;const b=$('dailyAlt');b.disabled=true;rewarded().then(ok=>{
    if(ok){const d=dayKey();save.dailyAlt={day:d,n:(save.dailyAlt&&save.dailyAlt.day===d?save.dailyAlt.n:0)+1};persist();renderDaily();}
    b.disabled=false;checkRewarded();});};
  $('hintBtn').onclick=()=>{if(!g||g.over||NET||anim||g.toMove()!==0||hintUsed)return;const b=$('hintBtn');b.disabled=true;rewarded().then(ok=>{
    b.disabled=false;if(!ok){checkRewarded();return;}hintUsed=true;refreshAdButtons();showHint();checkRewarded();});};}
let hintUsed=false;
// the move a strong player would make here, shown with a soft pulse
function showHint(){if(!g||g.over||g.toMove()!==0)return;let m=null;try{m=aiMove(g,0,STYLES.shrewd);}catch(e){}
  if(!m)return;document.querySelectorAll('.hint').forEach(e=>e.classList.remove('hint'));
  if(m.c&&els[m.c.id]){els[m.c.id].classList.add('hint');gToast(m.t==='transfer'?'Совет: переведите этой картой':m.t==='defend'?'Совет: отбейтесь этой картой':'Совет: ходите этой картой');}
  else gToast(m.t==='take'?'Совет: лучше взять':g.att===0?'Совет: пора сказать «Бито»':'Совет: лучше не подкидывать');
  setTimeout(()=>document.querySelectorAll('.hint').forEach(e=>e.classList.remove('hint')),6000);}
function refreshAdButtons(){if(!PF)return;
  $('giftAd').hidden=!rewardedOk;$('dailyAlt').hidden=!rewardedOk||dailyDone();
  $('hintBtn').hidden=!rewardedOk||!g||NET||hintUsed||!!(g&&g.over);}
const renderDaily0=renderDaily;renderDaily=function(){renderDaily0();refreshAdButtons();renderIapBar();};

/* --- an ordinary ad between games: not before the second game, at most every 3.5 minutes, never mid-game --- */
let lastFull=Date.now(),gamesHere=0;
const startGame0=startGame;
startGame=function(c){hintUsed=false;gamesHere++;
  const can=PF&&!noAds()&&gamesHere>1&&c.kind!=='online'&&Date.now()-lastFull>210000;
  if(!can){startGame0(c);refreshAdButtons();return;}
  lastFull=Date.now();withAd(()=>PF.fullscreen()).then(()=>{startGame0(c);refreshAdButtons();});};
if(PF){checkRewarded();setInterval(checkRewarded,60000);if(PF.started)PF.started();}

})();
