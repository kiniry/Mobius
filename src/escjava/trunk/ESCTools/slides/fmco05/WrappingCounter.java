/** 
 * A class of counters that count up to MAX and then wrap back to 0.
 * This class is specified using the Design-by-Contract approach.
 */

public class WrappingCounter {

    public final static int MAX = 100;
    private int count;

    //@ invariant 0 <= getCount() && getCount() <= MAX;

    /*@ requires 0 <= count && count <= MAX;
      @ ensures  getCount() == count;
      @ also
      @ requires !(0 <= count && count <= MAX);
      @ ensures getCount() == 0;
      @*/
    public WrappingCounter(int count) {
	this.count = count;
    }

    /*@ pure @*/ public int getCount() {
	return count;
    }

    /*@ requires getCount() < MAX;
      @ ensures  getCount() == \old(getCount()) + 1;
      @ also
      @ requires getCount() == MAX;
      @ ensures getCount() == 0;
      @*/
    public void inc() {
	count = count < MAX ? count + 1 : 0;
    }
}
