// from krml178, Section 1
type Wicket;
const w : Wicket;
function age(Wicket) returns (int);
axiom age(w)==7;

var favorite : Wicket;

procedure NewFavorite(n : Wicket);
  modifies favorite;
  ensures favorite == n;

implementation NewFavorite(n : Wicket) {
  favorite := n;
}

// from krml178, Section 2
type Barrel alpha;
type finite RGBColor;
const unique red : RGBColor;
const unique green : RGBColor;
const unique blue : RGBColor;
axiom (forall ce : RGBColor :: ce == red || ce == green || ce == blue);

const m : [Barrel Wicket] Wicket;
const n : <alpha> [Barrel alpha] alpha;
type C alpha beta;
const a : C Wicket Wicket;
// ERR: const b : Barrel Barrel Wicket
const c : Barrel (Barrel Wicket);
const d : Barrel [int] Barrel Wicket; // Barrel ([int] (Barrel Wicket))
// ERR: const e : C Wicket Barrel int;
const f : C Wicket (Barrel int);
const g : C Wicket [int] Barrel int; // C Wicket ([int](Barrel int))
// ERR: const h : C [int] int Wicket; // same as C ([int] (int Wicket))
// ERR: const i : C [int] Wicket Wicket;
const j : C ([int] Wicket) Wicket;

type MySynonym alpha = int;
type ComplicatedInt = MySynonym (MySynonym bool);
// ERR: type Bogus : MySynonym MySynonym;
type MultiSet alpha = [alpha] int;
type S alpha beta = <gamma> [beta, gamma] int;
const foo1 : S bool (S Wicket <gamma>[gamma]gamma);
const foo2 : <epsilon>[<delta>[<gamma>[gamma]gamma,delta]int, epsilon]int;
axiom foo1 == foo2; // check that the two types are the same
// ERR: const foo3 : <beta>[MySynonym beta] int; // beta must appear in the domain ???

// from krml178, Section 3
function volume<alpha>(Barrel alpha) returns (int);
function cylinderVolume(radius : int, height : int) returns (int) {
  radius * radius * height // almost
}

// from krml178, Section 4
axiom (forall x:int, y:int :: {x%y} x%y == x-x/y*y);
axiom (forall x:int, y:int :: {x%y}
  (0 < y ==> 0 <= x%y && x%y < y) &&
  (y < 0 ==> y < x%y %% x%y <= 0)); 
  // todo: allow a<b<c as a shortcut a<b && b<c

const a : [int, RGBColor] Wicket;
 // todo: check that maps aren't extensional

procedure foobar() returns () {
  assert (13bv6 ++ 4bv3)[5:2] == 3bv3;
  // todo: check that old() affects only globals: not locals, not out-arguments
  assert (forall t:Wicket :: age(t) <= 20);
  assert (forall<alpha> x:int, y:Barrel alpha :: true);
  assert (forall x:int :: (forall<alpha> y:Barrel alpha :: true));
  // ERR: assert (forall<alpha> x:int ::(forall y:Barrel alpha :: true)); // alpha must appear in the types of the outer quantifier!
  assert (exists<alpha> x:int, y:Barrel alpha :: true);
}

// from krml178, Section 5
type Ref;
var C0.data : [Ref]int;
var C0.next : [Ref]Ref;
var alloc0 : [Ref]bool;
type Field alpha;
type HeapType = <alpha>[Ref, Field alpha]alpha;
var Heap : HeapType;
const unique C.data : Field int;
const unique C.next : Field Ref;
const unique alloc : Field bool;
function C.m(heap:<alpha>[Ref,Field alpha]alpha, this:Ref) returns (bool);
var ObjStore : [Ref]<alpha>[Field alpha]alpha;
function D.m(this:Ref, dataRecord:<alpha>[Field alpha]alpha) returns (bool);

procedure foobar2() returns () 
  modifies Heap;
  ensures (forall<alpha> o:Ref, f:Field alpha ::
    Heap[o,f]==old(Heap)[o,f] ||
    (o==p && f==C.data) ||
    !old(Heap)[o,alloc]);
{}

// from krml178, Section 9
procedure foobar3(N:int, X:int) returns () {
  var x, y, i : int;
  var a : [int] int;
  var b : [int][int,int]int;
  x:=x+1;
  a[i]:=12;
  x,y:=y,x;
  x,a[i]:=x+1,x;
  // err: a[i],a[j]:=a[j],a[i]; // two a-s on the left
  b[i][x,y]:=10;
  b:=b[i:=b[i][m,n:=10]];
  i:=0;
  while (i<N) {
    if (a[i]==X) {break;} // why doesn't break this out of an if?
    i:=i+1;
  }
  i:=0;
  while (i<N) {
    if (a[i]==X) {goto Done;}
    i:=i+1;
  }
Done:
  i:=0;
Head:
  if (i<N) {
    if (a[i]==X) { goto Done2; }
    i := i+1;
    goto Head;
  }
Done2:
  i:=0;
Head2:
  if (i<N) {
    if (a[i]==X) {break Head2;} // 'break label' works for if too
    i:=i+1;
    goto Head2;
  }
}

