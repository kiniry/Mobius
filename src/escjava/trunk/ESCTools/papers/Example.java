public class Example {
    private int value;
    private Example min,max;

    //@ ensures \result == value < o.value;
    public boolean less(Example o);

    //@ requires min.less(max);
    //@ assignable min;
    //@ ensures !less(min);
    public void checkMin() {
        if (less(min)) min = this;
    }
}
