/* ESC/Java interface of java.lang.Object */

package java.lang;

public class Object {

    /**
     ** The Object that has a field pointing to this Object.
     ** Used to specify (among other things) injectivity (see
     ** the ESC/Java User's Manual.
     **/
    //@ ghost public Object owner;

    //@ ensures \result != null;
    public final native Class getClass();

    public native int hashCode();

    //@ ensures obj == null ==> !\result;
    public boolean equals(Object obj);

    //@ ensures \result != null;
    //@ ensures \typeof(\result) == \typeof(this);
    //@ ensures \result.owner == null;
    protected native Object clone() throws CloneNotSupportedException;

    //@ ensures \result != null;
    public String toString();

    public final native void notify();

    public final native void notifyAll();

    public final native void wait(long timeout) throws InterruptedException;

    //@ requires 0<=timeout;
    //@ requires 0<=nanos && nanos<=999999;
    public final void wait(long timeout, int nanos) throws InterruptedException;

    public final void wait() throws InterruptedException;

    protected void finalize() throws Throwable;
}
