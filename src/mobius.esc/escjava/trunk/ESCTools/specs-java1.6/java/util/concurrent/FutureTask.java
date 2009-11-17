package java.util.concurrent;

import java.util.concurrent.locks.*;

public class FutureTask implements Future, Runnable {
    private final FutureTask$Sync sync;
    
    public FutureTask(Callable callable) {
        
        if (callable == null) throw new NullPointerException();
        sync = new FutureTask$Sync(this, callable);
    }
    
    public FutureTask(Runnable runnable, Object result) {
        
        sync = new FutureTask$Sync(this, Executors.callable(runnable, result));
    }
    
    public boolean isCancelled() {
        return sync.innerIsCancelled();
    }
    
    public boolean isDone() {
        return sync.innerIsDone();
    }
    
    public boolean cancel(boolean mayInterruptIfRunning) {
        return sync.innerCancel(mayInterruptIfRunning);
    }
    
    public Object get() throws InterruptedException, ExecutionException {
        return sync.innerGet();
    }
    
    public Object get(long timeout, TimeUnit unit) throws InterruptedException, ExecutionException, TimeoutException {
        return sync.innerGet(unit.toNanos(timeout));
    }
    
    protected void done() {
    }
    
    protected void set(Object v) {
        sync.innerSet(v);
    }
    
    protected void setException(Throwable t) {
        sync.innerSetException(t);
    }
    
    public void run() {
        sync.innerRun();
    }
    
    protected boolean runAndReset() {
        return sync.innerRunAndReset();
    }
    {
    }
}
