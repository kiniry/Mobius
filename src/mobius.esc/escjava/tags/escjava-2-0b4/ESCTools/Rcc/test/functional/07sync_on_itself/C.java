public class C {
  public final static Object lock = new Object();
  
  public void doit() {
    synchronized (C.lock) {  // should be OK because locks are final
      C.lock.toString();
    }
  }
}
