procedure swap(x : int, y : int) returns (xx : int, yy : int);
  ensures xx == old(y);
  ensures yy == old(x);

// NOK
implementation swap(a : int, b : int) returns (aa : int, bb : int) {
  start:
    aa := a;
    bb := b;
    return;
}

// OK
implementation swap(a : int, b : int) returns (aa : int, bb : int) {
  start:
    aa := b;
    bb := a;
    return;
}

// OK
implementation swap(y : int, x : int) returns (xx : int, yy : int) {
  start:
    xx := x;
    yy := y;
    return;
}

// NOK
implementation swap(yy : int, xx : int) returns (x : int, y : int) {
  start:
    xx := x;
    yy := y;
    return;
}


