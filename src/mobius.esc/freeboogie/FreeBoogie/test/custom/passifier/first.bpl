var heap<x> : [ref, <x>name]x;
var r : ref;
var f : <ref>name;
var f' : <int>name;

procedure a(a : [int]int) returns (x: int)
{
    var i: int;
    var t: int;
	a:
		i := x + 1;
		goto b;
	b:  x := x + 2;
	   goto c, d;
	c: x:= x + 3;
	   goto d;
	d: x:= x + 4;
	   goto e;
	e: i := x + 5;
	   goto f, g;
	f: x:= x + 6;
	   goto h;
	g: x:= 1;
	   goto h;
	h: x:= 3;
	   return;
}

