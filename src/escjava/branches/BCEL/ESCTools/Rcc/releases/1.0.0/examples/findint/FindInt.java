import java.util.List;
import java.util.Iterator;

interface IntegerProperty {
  public boolean ok(Integer x);
}

/** 
    A thread that finds an Integer that satisfies a given property.
 */
class Worker extends Thread {
  private List integers;
  private IntegerProperty property;
  private Integer result;
  private boolean isOver;

  private static Integer dummyAnswer = new Integer(-1);
  
  public Worker(List integers, IntegerProperty property){
    this.integers = integers;
    this.property = property;
    this.result = result;
    this.isOver = false;
  }

  public void run() {
    Iterator it = integers.iterator();
    while (it.hasNext()) {
      Integer x = (Integer)it.next();
      if (property.ok(x)) {
        result = x;
        break;
      }
    }
    isOver = true; // if not volatile, can be moved before loop
  }

  public boolean isOver() { return isOver; }
  public Integer getResult() { return result; }
}


class Finder {
  /**
     If there is no x in a and b such that p.ok(x) then
     return null. Otherwise return some x p.ok(x).
   */
  public Integer find(List a, List b, IntegerProperty p) {
    Worker wa = new Worker(a, p); // not related to the city
    Worker wb = new Worker(b, p);
    wa.start(); wb.start();
    Integer ra, rb;
    boolean oa, ob;
    do {
      ra = wa.getResult(); oa = wa.isOver();
      rb = wb.getResult(); ob = wb.isOver();
    } while (ra==null && rb==null && (!oa || !ob));
    if (ra != null) return ra;
    if (rb != null) return rb;
    return null;
  }
}
