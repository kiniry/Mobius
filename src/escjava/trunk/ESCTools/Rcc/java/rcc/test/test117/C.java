

class D /*# {ghost Object o}  */ {
     public D/*#{o}*/ f(int a)
    {
        return null;
    }
}


class C {
    final Object x;
    D/*#{this.x}*/ dd;
    void f() {        
        dd.f(2);
    }
}







//class D /*# {ghost Object o}  */ {
//   public D/*#{o}*/ f(int a) /* requires o */
//  {
//return null;
////            return this;
//  }
//  //    public int a /*# guarded_by o */;

//}


//class C {
// Object x;
//  //    Object y;
//  D/*#{this.x}*/ dd;
//  //D/*#{this.y}*/ ddee;
//  void f() {        
////D/*#{this.x}*/ g;
////D/*#{this.x}*/ h = new D/*#{this.x}*/();
//dd.a = 2;//g.a = 2;
////g = h.f();
//  }
//}
