package java.lang;

public enum Thread$State extends Enum<Thread$State> {
    /*public static final*/ NEW /* = new Thread$State("NEW", 0) */,
    /*public static final*/ RUNNABLE /* = new Thread$State("RUNNABLE", 1) */,
    /*public static final*/ BLOCKED /* = new Thread$State("BLOCKED", 2) */,
    /*public static final*/ WAITING /* = new Thread$State("WAITING", 3) */,
    /*public static final*/ TIMED_WAITING /* = new Thread$State("TIMED_WAITING", 4) */,
    /*public static final*/ TERMINATED /* = new Thread$State("TERMINATED", 5) */;
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
