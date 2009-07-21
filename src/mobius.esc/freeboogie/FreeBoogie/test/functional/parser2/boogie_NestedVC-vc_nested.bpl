type name;
type ref;
const unique null : ref;
procedure P();
implementation P() {
  A: goto B, C;
  B: goto G;
  C: goto D, E;
  D: goto F;
  E: goto F;
  F: goto G;
  G: return;
  
}

procedure Q(x : bool);
implementation Q(x : bool) {
  A: goto B, C;
  B: assert x; goto G;
  C: goto D, E;
  D: goto F;
  E: goto F;
  F: goto G;
  G: return;
  
}

