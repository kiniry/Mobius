procedure evil<x,y,z>(a : [x][y]z, i : x) returns (r : [y]z) {
  entry:
    r := a[i];
    return;
}
