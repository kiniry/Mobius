
public class C {
    public static final Object o;
    static String s /*# guarded_by F.a */;
}

class F  {
    public static final Object a;
    static String s /*# guarded_by C.o */;
}

class G {
    void f() {
        F.s = "123";
    }
}
