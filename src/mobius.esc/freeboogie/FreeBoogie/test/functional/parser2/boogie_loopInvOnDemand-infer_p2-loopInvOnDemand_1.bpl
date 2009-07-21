type name;
type ref;
const unique null : ref;
procedure M(N : int);
implementation M(N : int) {
  var i : int;
  var m : int;
  var N$in : int;
  start: N$in := N; goto $$start~b;
  $$start~b: i := 0; goto $$start~a;
  $$start~a: m := 0; goto body, id$end;
  body: assume (i < N); goto id$then, id$else;
  id$then: m := i; goto join;
  id$else: goto join;
  join: i := (i + 1); goto body, id$end, JoinCheck;
  JoinCheck: assert ((((i <= N) && (0 <= m)) && (1 <= i)) && (m < N)); return;
  id$end: goto checkIfNgz, realEnd;
  checkIfNgz: assume (N > 0); goto $$checkIfNgz~a;
  $$checkIfNgz~a: assert ((0 <= m) && (m < N)); goto realEnd;
  realEnd: return;
  
}

