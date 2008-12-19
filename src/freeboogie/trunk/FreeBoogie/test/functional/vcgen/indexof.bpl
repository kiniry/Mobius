procedure indexOf(x : int, a : [int] int, al : int) returns (i : int) {
  A: i := 0; goto B, D;
  B: assume i < al && a[i] != x; goto C;
  C: i := i + 1; goto B, D;
  D: assume !(i < al && a[i] != x); return;
}
