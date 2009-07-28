

class F {
    public static final Object d;
    public static  Object e;
   public static  Object ej[];
}


class D /*# {ghost Object o}  */ {
    public int a /*# guarded_by o */;
}


class C {
    D/*#{F.d}*/ dd; 
    D/*#{F.e}*/ ee;
    void f() {
	synchronized(F.d) {
	    dd.a = 2;
	    dd = ee;
	    dd.a=ee.a;
		}
    }
}

 

class J extends D/*#{F.e}*/ {
    C c;
    DD/*#{null,c}*/ x;
}


class DD /*# {ghost Object o, C z}  */ {
    public int a /*# guarded_by o,z */;
}

class Js extends D/*#{F.e,F.ej[2]}*/ {

}
