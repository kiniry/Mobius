package java.lang;

public class Thread$State extends Enum {
    public static final Thread$State NEW  = new Thread$State("NEW", 0);
    public static final Thread$State RUNNABLE  = new Thread$State("RUNNABLE", 1);
    public static final Thread$State BLOCKED  = new Thread$State("BLOCKED", 2);
    public static final Thread$State WAITING  = new Thread$State("WAITING", 3);
    public static final Thread$State TIMED_WAITING  = new Thread$State("TIMED_WAITING", 4);
    public static final Thread$State TERMINATED  = new Thread$State("TERMINATED", 5);
    /*synthetic*/ private static final Thread$State[] $VALUES = new Thread$State[]{Thread$State.NEW, Thread$State.RUNNABLE, Thread$State.BLOCKED, Thread$State.WAITING, Thread$State.TIMED_WAITING, Thread$State.TERMINATED};
    
    public static final Thread$State[] values() {
        return (Thread$State[])$VALUES.clone();
    }
    
    public static Thread$State valueOf(String name) {
        return (Thread$State)Enum.valueOf(Thread.State.class, name);
    }
    
    private Thread$State(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal) {
        super($enum$name, $enum$ordinal);
    }
}
