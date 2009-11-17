package java.util.concurrent.locks;

import java.util.concurrent.*;
import sun.misc.Unsafe;

public class LockSupport {
    
    private LockSupport() {
        
    }
    private static final Unsafe unsafe = Unsafe.getUnsafe();
    
    public static void unpark(Thread thread) {
        if (thread != null) unsafe.unpark(thread);
    }
    
    public static void park() {
        unsafe.park(false, 0L);
    }
    
    public static void parkNanos(long nanos) {
        if (nanos > 0) unsafe.park(false, nanos);
    }
    
    public static void parkUntil(long deadline) {
        unsafe.park(true, deadline);
    }
}
