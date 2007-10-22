
public class C {
    int i;
    String s /*# guarded_by this */;
    C o /*# guarded_by s */;
    C oo /*# guarded_by s */  /*# guarded_by this
          */;
    
    final String  fs;
    Object v /*# guarded_by fs */;
    
    
    
    /*# requires this */ 
    public void  f() {
        
        s = "asd";
    }
    
    /*# guarded_by fs */
    public void  f() {
        
        s = "asd";
    }
    
    
    public void  g() /*# requires this */ {
        synchronized(s) {
            o.i =3;
            synchronized(o) {
                o.s.toString();
            }
        }
    }
    /*# guarded_by s */
    public void  h() {
        C o /*# guarded_by s */;
        s = "asd";
    }
    
}
