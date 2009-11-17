package java.util.concurrent;

import java.util.concurrent.locks.*;

final class FutureTask$Sync extends AbstractQueuedSynchronizer {
    /*synthetic*/ final FutureTask this$0;
    private static final int RUNNING = 1;
    private static final int RAN = 2;
    private static final int CANCELLED = 4;
    private final Callable callable;
    private Object result;
    private Throwable exception;
    private volatile Thread runner;
    
    FutureTask$Sync(/*synthetic*/ final FutureTask this$0, Callable callable) {
        this.this$0 = this$0;
        
        this.callable = callable;
    }
    
    private boolean ranOrCancelled(int state) {
        return (state & (RAN | CANCELLED)) != 0;
    }
    
    protected int tryAcquireShared(int ignore) {
        return innerIsDone() ? 1 : -1;
    }
    
    protected boolean tryReleaseShared(int ignore) {
        runner = null;
        return true;
    }
    
    boolean innerIsCancelled() {
        return getState() == CANCELLED;
    }
    
    boolean innerIsDone() {
        return ranOrCancelled(getState()) && runner == null;
    }
    
    Object innerGet() throws InterruptedException, ExecutionException {
        acquireSharedInterruptibly(0);
        if (getState() == CANCELLED) throw new CancellationException();
        if (exception != null) throw new ExecutionException(exception);
        return result;
    }
    
    Object innerGet(long nanosTimeout) throws InterruptedException, ExecutionException, TimeoutException {
        if (!tryAcquireSharedNanos(0, nanosTimeout)) throw new TimeoutException();
        if (getState() == CANCELLED) throw new CancellationException();
        if (exception != null) throw new ExecutionException(exception);
        return result;
    }
    
    void innerSet(Object v) {
        for (; ; ) {
            int s = getState();
            if (ranOrCancelled(s)) return;
            if (compareAndSetState(s, RAN)) break;
        }
        result = v;
        releaseShared(0);
        this$0.done();
    }
    
    void innerSetException(Throwable t) {
        for (; ; ) {
            int s = getState();
            if (ranOrCancelled(s)) return;
            if (compareAndSetState(s, RAN)) break;
        }
        exception = t;
        result = null;
        releaseShared(0);
        this$0.done();
    }
    
    boolean innerCancel(boolean mayInterruptIfRunning) {
        for (; ; ) {
            int s = getState();
            if (ranOrCancelled(s)) return false;
            if (compareAndSetState(s, CANCELLED)) break;
        }
        if (mayInterruptIfRunning) {
            Thread r = runner;
            if (r != null) r.interrupt();
        }
        releaseShared(0);
        this$0.done();
        return true;
    }
    
    void innerRun() {
        if (!compareAndSetState(0, RUNNING)) return;
        try {
            runner = Thread.currentThread();
            innerSet(callable.call());
        } catch (Throwable ex) {
            innerSetException(ex);
        }
    }
    
    boolean innerRunAndReset() {
        if (!compareAndSetState(0, RUNNING)) return false;
        try {
            runner = Thread.currentThread();
            callable.call();
            runner = null;
            return compareAndSetState(RUNNING, 0);
        } catch (Throwable ex) {
            innerSetException(ex);
            return false;
        }
    }
}
