
interface I   {
                public void f() /*# requires this */;                
                                }


/*# thread_local */
interface Ii  extends I {
                public void j() /*# requires this */;                
                                }

/*# thread_local */
public class C  {
}

/*# thread_shared */
class D implements I {
                public void f(){}
}

/*# thread_local  */
class F extends C implements I{
                public void f(){}
}


/*# thread_shared */
class Dd implements Ii {
                public void f() /*# requires this,Dd.class */{}
}
