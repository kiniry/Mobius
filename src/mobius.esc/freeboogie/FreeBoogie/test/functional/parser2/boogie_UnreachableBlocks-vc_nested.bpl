type name;
type ref;
const unique null : ref;
procedure P();
implementation P() {
  entry: goto A;
  A: return;
  B: goto A;
  
}

procedure Q();
implementation Q() {
  entry: goto entry, A;
  A: return;
  
}

procedure R();
implementation R() {
  entry: return;
  A: goto A;
  
}

procedure S();
implementation S() {
  entry: return;
  A: goto C;
  B: goto C;
  C: return;
  
}

