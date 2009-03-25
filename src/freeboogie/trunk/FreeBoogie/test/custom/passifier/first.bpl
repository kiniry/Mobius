var heap<x> : [ref, <x>name]x;
var r : ref;
var f : <ref>name;
var f' : <int>name;

procedure a(a : [int]int) returns (x: int)
{
    var i: int;
	a:
		i := x + 1;
		goto b, e;
	b:  x := x + 2;
	   goto c;
	c: x:= x + 3;
	   goto d;
	d: x:= x + 4;
	   goto f;
	e: i := x + 5;
	   goto f;
	f: x:= x + 6;
	   return;
}

