public class Example {
    private int value;
    static private Example min,max;
    //@ requires o != null;
    //@ ensures \result == value < o.value;
    //@ signals (Exception) false; diverges false;
    /*@ pure */ public boolean less(Example o);

    //@ requires min.less(max);
    //@ assignable min;
    //@ ensures !less(min);
    public void accumulateMin() {
        if (less(min)) min = this;
    }
}
