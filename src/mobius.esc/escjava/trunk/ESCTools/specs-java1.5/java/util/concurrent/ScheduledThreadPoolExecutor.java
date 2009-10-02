package java.util.concurrent;

import java.util.concurrent.atomic.*;
import java.util.*;

public class ScheduledThreadPoolExecutor extends ThreadPoolExecutor implements ScheduledExecutorService {
    
    /*synthetic*/ static BlockingQueue access$201(ScheduledThreadPoolExecutor x0) {
        return x0.getQueue();
    }
    
    /*synthetic*/ static AtomicLong access$000() {
        return sequencer;
    }
    {
    }
    private volatile boolean continueExistingPeriodicTasksAfterShutdown;
    private volatile boolean executeExistingDelayedTasksAfterShutdown = true;
    private static final AtomicLong sequencer = new AtomicLong(0);
    private static final long NANO_ORIGIN = System.nanoTime();
    
    final long now() {
        return System.nanoTime() - NANO_ORIGIN;
    }
    {
    }
    
    private void delayedExecute(Runnable command) {
        if (isShutdown()) {
            reject(command);
            return;
        }
        if (getPoolSize() < getCorePoolSize()) prestartCoreThread();
        super.getQueue().add(command);
    }
    
    private void cancelUnwantedTasks() {
        boolean keepDelayed = getExecuteExistingDelayedTasksAfterShutdownPolicy();
        boolean keepPeriodic = getContinueExistingPeriodicTasksAfterShutdownPolicy();
        if (!keepDelayed && !keepPeriodic) super.getQueue().clear(); else if (keepDelayed || keepPeriodic) {
            Object[] entries = super.getQueue().toArray();
            for (int i = 0; i < entries.length; ++i) {
                Object e = entries[i];
                if (e instanceof ScheduledThreadPoolExecutor$ScheduledFutureTask) {
                    ScheduledThreadPoolExecutor$ScheduledFutureTask t = (ScheduledThreadPoolExecutor$ScheduledFutureTask)(ScheduledThreadPoolExecutor$ScheduledFutureTask)e;
                    if (t.isPeriodic() ? !keepPeriodic : !keepDelayed) t.cancel(false);
                }
            }
            entries = null;
            purge();
        }
    }
    
    public boolean remove(Runnable task) {
        if (!(task instanceof ScheduledThreadPoolExecutor$ScheduledFutureTask)) return false;
        return getQueue().remove(task);
    }
    
    public ScheduledThreadPoolExecutor(int corePoolSize) {
        super(corePoolSize, Integer.MAX_VALUE, 0, TimeUnit.NANOSECONDS, new ScheduledThreadPoolExecutor$DelayedWorkQueue(null));
    }
    
    public ScheduledThreadPoolExecutor(int corePoolSize, ThreadFactory threadFactory) {
        super(corePoolSize, Integer.MAX_VALUE, 0, TimeUnit.NANOSECONDS, new ScheduledThreadPoolExecutor$DelayedWorkQueue(null), threadFactory);
    }
    
    public ScheduledThreadPoolExecutor(int corePoolSize, RejectedExecutionHandler handler) {
        super(corePoolSize, Integer.MAX_VALUE, 0, TimeUnit.NANOSECONDS, new ScheduledThreadPoolExecutor$DelayedWorkQueue(null), handler);
    }
    
    public ScheduledThreadPoolExecutor(int corePoolSize, ThreadFactory threadFactory, RejectedExecutionHandler handler) {
        super(corePoolSize, Integer.MAX_VALUE, 0, TimeUnit.NANOSECONDS, new ScheduledThreadPoolExecutor$DelayedWorkQueue(null), threadFactory, handler);
    }
    
    private long triggerTime(long delay, TimeUnit unit) {
        return triggerTime(unit.toNanos((delay < 0) ? 0 : delay));
    }
    
    long triggerTime(long delay) {
        return now() + ((delay < (Long.MAX_VALUE >> 1)) ? delay : overflowFree(delay));
    }
    
    private long overflowFree(long delay) {
        Delayed head = (Delayed)(Delayed)super.getQueue().peek();
        if (head != null) {
            long headDelay = head.getDelay(TimeUnit.NANOSECONDS);
            if (headDelay < 0 && (delay - headDelay < 0)) delay = Long.MAX_VALUE + headDelay;
        }
        return delay;
    }
    
    public ScheduledFuture schedule(Runnable command, long delay, TimeUnit unit) {
        if (command == null || unit == null) throw new NullPointerException();
        ScheduledThreadPoolExecutor$ScheduledFutureTask t = new ScheduledThreadPoolExecutor$ScheduledFutureTask(this, command, null, triggerTime(delay, unit));
        delayedExecute(t);
        return t;
    }
    
    public ScheduledFuture schedule(Callable callable, long delay, TimeUnit unit) {
        if (callable == null || unit == null) throw new NullPointerException();
        ScheduledThreadPoolExecutor$ScheduledFutureTask t = new ScheduledThreadPoolExecutor$ScheduledFutureTask(this, callable, triggerTime(delay, unit));
        delayedExecute(t);
        return t;
    }
    
    public ScheduledFuture scheduleAtFixedRate(Runnable command, long initialDelay, long period, TimeUnit unit) {
        if (command == null || unit == null) throw new NullPointerException();
        if (period <= 0) throw new IllegalArgumentException();
        ScheduledThreadPoolExecutor$ScheduledFutureTask t = new ScheduledThreadPoolExecutor$ScheduledFutureTask(this, command, null, triggerTime(initialDelay, unit), unit.toNanos(period));
        delayedExecute(t);
        return t;
    }
    
    public ScheduledFuture scheduleWithFixedDelay(Runnable command, long initialDelay, long delay, TimeUnit unit) {
        if (command == null || unit == null) throw new NullPointerException();
        if (delay <= 0) throw new IllegalArgumentException();
        ScheduledThreadPoolExecutor$ScheduledFutureTask t = new ScheduledThreadPoolExecutor$ScheduledFutureTask(this, command, null, triggerTime(initialDelay, unit), unit.toNanos(-delay));
        delayedExecute(t);
        return t;
    }
    
    public void execute(Runnable command) {
        if (command == null) throw new NullPointerException();
        schedule(command, 0, TimeUnit.NANOSECONDS);
    }
    
    public Future submit(Runnable task) {
        return schedule(task, 0, TimeUnit.NANOSECONDS);
    }
    
    public Future submit(Runnable task, Object result) {
        return schedule(Executors.callable(task, result), 0, TimeUnit.NANOSECONDS);
    }
    
    public Future submit(Callable task) {
        return schedule(task, 0, TimeUnit.NANOSECONDS);
    }
    
    public void setContinueExistingPeriodicTasksAfterShutdownPolicy(boolean value) {
        continueExistingPeriodicTasksAfterShutdown = value;
        if (!value && isShutdown()) cancelUnwantedTasks();
    }
    
    public boolean getContinueExistingPeriodicTasksAfterShutdownPolicy() {
        return continueExistingPeriodicTasksAfterShutdown;
    }
    
    public void setExecuteExistingDelayedTasksAfterShutdownPolicy(boolean value) {
        executeExistingDelayedTasksAfterShutdown = value;
        if (!value && isShutdown()) cancelUnwantedTasks();
    }
    
    public boolean getExecuteExistingDelayedTasksAfterShutdownPolicy() {
        return executeExistingDelayedTasksAfterShutdown;
    }
    
    public void shutdown() {
        cancelUnwantedTasks();
        super.shutdown();
    }
    
    public List shutdownNow() {
        return super.shutdownNow();
    }
    
    public BlockingQueue getQueue() {
        return super.getQueue();
    }
    {
    }
}
