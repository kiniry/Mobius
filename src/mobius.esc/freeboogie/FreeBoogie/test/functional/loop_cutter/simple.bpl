procedure P(a : [int]int, x : int) returns (i : int) {
  entry:
    i := 0;
    goto head;
  head:
    goto body, after;
  body:
    assume a[i] != x;
    i := i + 1;
    goto head;
  after:
    assume a[i] == x;
    return;
}
