abstract class DummyBill {
  
  
   //@ requires n > 0;
   //@ ensures true;
   // assignable \nothing;
  public boolean produce(int n) {
    int i = n;
    //@ loop_invariant i <= n + 1;
    for (i = 1; i <= n; i++) {
    }
    return true;

  }
}
