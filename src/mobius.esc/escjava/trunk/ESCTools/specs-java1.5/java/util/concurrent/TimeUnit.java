package java.util.concurrent;

public class TimeUnit extends Enum {
    public static final TimeUnit NANOSECONDS  = new TimeUnit("NANOSECONDS", 0, 0) ;
    public static final TimeUnit MICROSECONDS  = new TimeUnit("MICROSECONDS", 1, 1) ;
    public static final  TimeUnit MILLISECONDS  = new TimeUnit("MILLISECONDS", 2, 2) ;
    public static final  TimeUnit SECONDS  = new TimeUnit("SECONDS", 3, 3);
    /*synthetic*/ private static final TimeUnit[] $VALUES = new TimeUnit[]{TimeUnit.NANOSECONDS, TimeUnit.MICROSECONDS, TimeUnit.MILLISECONDS, TimeUnit.SECONDS};
    
    public static final TimeUnit[] values() {
        return (TimeUnit[])$VALUES.clone();
    }
    
    public static TimeUnit valueOf(String name) {
        return (TimeUnit)Enum.valueOf(TimeUnit.class, name);
    }
    private final int index;
    
    TimeUnit(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal, int index) {
        super($enum$name, $enum$ordinal);
        this.index = index;
    }
    private static final int[] multipliers = {1, 1000, 1000 * 1000, 1000 * 1000 * 1000};
    private static final long[] overflows = {0, Long.MAX_VALUE / 1000, Long.MAX_VALUE / (1000 * 1000), Long.MAX_VALUE / (1000 * 1000 * 1000)};
    
    private static long doConvert(int delta, long duration) {
        if (delta == 0) return duration;
        if (delta < 0) return duration / multipliers[-delta];
        if (duration > overflows[delta]) return Long.MAX_VALUE;
        if (duration < -overflows[delta]) return Long.MIN_VALUE;
        return duration * multipliers[delta];
    }
    
    public long convert(long duration, TimeUnit unit) {
        return doConvert(unit.index - index, duration);
    }
    
    public long toNanos(long duration) {
        return doConvert(index, duration);
    }
    
    public long toMicros(long duration) {
        return doConvert(index - MICROSECONDS.index, duration);
    }
    
    public long toMillis(long duration) {
        return doConvert(index - MILLISECONDS.index, duration);
    }
    
    public long toSeconds(long duration) {
        return doConvert(index - SECONDS.index, duration);
    }
    
    private int excessNanos(long time, long ms) {
        if (this == NANOSECONDS) return (int)(time - (ms * 1000 * 1000));
        if (this == MICROSECONDS) return (int)((time * 1000) - (ms * 1000 * 1000));
        return 0;
    }
    
    public void timedWait(Object obj, long timeout) throws InterruptedException {
        if (timeout > 0) {
            long ms = toMillis(timeout);
            int ns = excessNanos(timeout, ms);
            obj.wait(ms, ns);
        }
    }
    
    public void timedJoin(Thread thread, long timeout) throws InterruptedException {
        if (timeout > 0) {
            long ms = toMillis(timeout);
            int ns = excessNanos(timeout, ms);
            thread.join(ms, ns);
        }
    }
    
    public void sleep(long timeout) throws InterruptedException {
        if (timeout > 0) {
            long ms = toMillis(timeout);
            int ns = excessNanos(timeout, ms);
            Thread.sleep(ms, ns);
        }
    }
}
