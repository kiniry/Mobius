package java.util.concurrent;

import java.util.*;

class Executors$DelegatedScheduledExecutorService extends Executors$DelegatedExecutorService implements ScheduledExecutorService {
    private final ScheduledExecutorService e;
    
    Executors$DelegatedScheduledExecutorService(ScheduledExecutorService executor) {
        super(executor);
        e = executor;
    }
    
    public ScheduledFuture schedule(Runnable command, long delay, TimeUnit unit) {
        return e.schedule(command, delay, unit);
    }
    
    public ScheduledFuture schedule(Callable callable, long delay, TimeUnit unit) {
        return e.schedule(callable, delay, unit);
    }
    
    public ScheduledFuture scheduleAtFixedRate(Runnable command, long initialDelay, long period, TimeUnit unit) {
        return e.scheduleAtFixedRate(command, initialDelay, period, unit);
    }
    
    public ScheduledFuture scheduleWithFixedDelay(Runnable command, long initialDelay, long delay, TimeUnit unit) {
        return e.scheduleWithFixedDelay(command, initialDelay, delay, unit);
    }
}
