package java.util.concurrent;

import java.util.concurrent.atomic.*;
import java.util.*;

class ScheduledThreadPoolExecutor$ScheduledFutureTask extends FutureTask implements ScheduledFuture {
    
    /*synthetic*/ static void access$301(ScheduledThreadPoolExecutor$ScheduledFutureTask x0) {
        x0.run();
    }
    
    /*synthetic*/ static boolean access$101(ScheduledThreadPoolExecutor$ScheduledFutureTask x0) {
        return x0.runAndReset();
    }
    /*synthetic*/ final ScheduledThreadPoolExecutor this$0;
    private final long sequenceNumber;
    private long time;
    private final long period;
    
    ScheduledThreadPoolExecutor$ScheduledFutureTask(/*synthetic*/ final ScheduledThreadPoolExecutor this$0, Runnable r, Object result, long ns) {
        super(r, result);
        this.this$0 = this$0;
    	this.time = ns;
        this.period = 0;
        this.sequenceNumber = ScheduledThreadPoolExecutor.access$000().getAndIncrement();
    }
    
    ScheduledThreadPoolExecutor$ScheduledFutureTask(/*synthetic*/ final ScheduledThreadPoolExecutor this$0, Runnable r, Object result, long ns, long period) {
        super(r, result);
        this.this$0 = this$0;
	this.time = ns;
        this.period = period;
        this.sequenceNumber = ScheduledThreadPoolExecutor.access$000().getAndIncrement();
    }
    
    ScheduledThreadPoolExecutor$ScheduledFutureTask(/*synthetic*/ final ScheduledThreadPoolExecutor this$0, Callable callable, long ns) {
        super(callable);
        this.this$0 = this$0;
	this.time = ns;
        this.period = 0;
        this.sequenceNumber = ScheduledThreadPoolExecutor.access$000().getAndIncrement();
    }
    
    public long getDelay(TimeUnit unit) {
        return unit.convert(time - this$0.now(), TimeUnit.NANOSECONDS);
    }
    
    public int compareTo(Delayed other) {
        if (other == this) return 0;
        if (other instanceof ScheduledThreadPoolExecutor$ScheduledFutureTask) {
            ScheduledThreadPoolExecutor$ScheduledFutureTask x = (ScheduledThreadPoolExecutor$ScheduledFutureTask)(ScheduledThreadPoolExecutor$ScheduledFutureTask)other;
            long diff = time - x.time;
            if (diff < 0) return -1; else if (diff > 0) return 1; else if (sequenceNumber < x.sequenceNumber) return -1; else return 1;
        }
        long d = (getDelay(TimeUnit.NANOSECONDS) - other.getDelay(TimeUnit.NANOSECONDS));
        return (d == 0) ? 0 : ((d < 0) ? -1 : 1);
    }
    
    boolean isPeriodic() {
        return period != 0;
    }
    
    private void runPeriodic() {
        boolean ok = ScheduledThreadPoolExecutor.ScheduledFutureTask.access$101(this);
        boolean down = this$0.isShutdown();
        if (ok && (!down || (this$0.getContinueExistingPeriodicTasksAfterShutdownPolicy() && !this$0.isTerminating()))) {
            long p = period;
            if (p > 0) time += p; else time = this$0.triggerTime(-p);
            ScheduledThreadPoolExecutor.access$201(this$0).add(this);
        } else if (down) this$0.interruptIdleWorkers();
    }
    
    public void run() {
        if (isPeriodic()) runPeriodic(); else ScheduledThreadPoolExecutor.ScheduledFutureTask.access$301(this);
    }
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((Delayed)x0);
    }
}
