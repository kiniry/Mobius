/** */
public class Test{
  /** */
  public  int k;
  /** */
  public Test() { }

  /*@
    @ ensures (\old(k) + 1 == k)  && (\forall Test o; o != this ==> o.k == \old(o.k));
    @*/
  public void inc() {
    k = k + 1;
  }

}
