type name;
type ref;
const unique null : ref;
var H : [ref, name]int;
var that : ref;
const X : name;
const Y : name;
procedure P(this : ref);
  modifies H;
  ensures (H[this, X] == 5);
  

implementation P(this : ref) {
  start: H := H[this, X := 5]; return;
  
}

procedure Q(this : ref);
  modifies H;
  ensures (forall o : ref, F : name :: (((o == this) && (F == X)) ==> (H[o, F] == 5)));
  

implementation Q(this : ref) {
  start: H := H[this, X := 5]; return;
  
}

implementation Q(this : ref) {
  start: H := H[this, X := 7]; return;
  
}

implementation Q(this : ref) {
  start: return;
  
}

implementation Q(this : ref) {
  start: H := H[that, X := 5]; return;
  
}

implementation Q(this : ref) {
  start: H := H[this, Y := 5]; return;
  
}

implementation Q(this : ref) {
  start: call P(this); return;
  
}

implementation Q(this : ref) {
  start: call Q(this); return;
  
}

implementation Q(this : ref) {
  start: call P(this); goto $$start~a;
  $$start~a: call Q(this); return;
  
}

implementation Q(this : ref) {
  start: call P(that); return;
  
}

