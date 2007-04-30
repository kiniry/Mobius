
public class C {
    static final String s;
    C() {
        new C(this);
    }
    
    C(C c) /*#requires C.s */ {}
}


class F  {
    void f() {
        C b = new C();
        C c = new C();
        synchronized (C.s) {
            new C(b);
        }
        new C(b);
    }
}

