package tests.methodspecs;

abstract class Test3 {
  private int sum;
 
  //@ modifies \nothing;
  //@ ensures \result <= x;
  abstract int round_cost(int x) throws Exception;
  
  /**
   * This method calculates the cost of the whole series of
   * investments.
   *
   * @return <code>true</code> when the calculation is successful and
   * <code>false</code> when the calculation cannot be performed.
   */
  //@ requires 0 < n;
  //@ ensures sum <=  \old(sum) + n*(n+1)/2;
  public boolean produce_bill(final int n) {
    int i = 0;
    try {
      for (i = 1; i <= n; i++) {
        sum = sum + round_cost(i);
      }
      return true;
    } 
    catch (Exception e) {
      return false;
    }
  }
}