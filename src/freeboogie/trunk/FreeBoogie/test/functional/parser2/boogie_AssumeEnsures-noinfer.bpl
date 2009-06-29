type name;
type ref;
const unique null : ref;
var g : int;
procedure Foo();
  modifies g;
  free ensures (0 <= g);
  

implementation Foo() {
  entry: g := (g + 1); return;
  
}

procedure BarGood();
  modifies g;
  

implementation BarGood() {
  entry: call Foo(); goto $$entry~a;
  $$entry~a: assert (0 <= g); return;
  
}

procedure BarBad();
  modifies g;
  

implementation BarBad() {
  entry: call Foo(); goto $$entry~b;
  $$entry~b: assert (0 < g); return;
  
}

procedure Proc();
  free requires (g == 15);
  

implementation Proc() {
  entry: assert (g > 10); return;
  
}

implementation Proc() {
  entry: assert (g < 10); return;
  
}

procedure Caller0();
implementation Caller0() {
  entry: call Proc(); return;
  
}

procedure Caller1();
implementation Caller1() {
  entry: call Proc(); goto $$entry~c;
  $$entry~c: assert (g > 10); return;
  
}

