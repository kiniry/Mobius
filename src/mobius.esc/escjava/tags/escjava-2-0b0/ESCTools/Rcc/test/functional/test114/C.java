
class D /*# {ghost Object o}  */ {
    public void  f/* {ghost Object s}  */(int a[]) /* requires s */
    {
    }
    public int a /*# guarded_by o */;
}


class F {
    public static final Object d;
}


class C {
    D/*#{F.d}*/ dd;
    void f() {
        dd.a = 2;
        
        synchronized(F.d) {
            dd.a = 2;
        }
    }
}


class GG {
    Object z;
    D/*#{z}*/ dd;
    void f() /*# requires z */{
        dd.a = 2;
    }
}

class G /*# {ghost Object o}  */ {
    D/*#{o}*/ dd;
    void f() /*# requires o */{
        dd.a = 2;
    }
}
