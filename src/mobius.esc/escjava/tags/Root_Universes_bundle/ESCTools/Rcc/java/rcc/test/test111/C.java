
/*# thread_local */
public class C {
    static final String s;
    C() { }

}




/*# thread_shared */
class D {
    static String s,t;
                static final String s2;
}

/*# thread_local */
class F  {
                final static String s;
                static String s2;
                String g /*# guarded_by this */;
}


class C2 {
    static final String s;
}
