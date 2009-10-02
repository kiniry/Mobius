package java.util.concurrent;

import java.util.*;

class Executors$DelegatedExecutorService extends AbstractExecutorService {
    private final ExecutorService e;
    
    Executors$DelegatedExecutorService(ExecutorService executor) {
        
        e = executor;
    }
    
    public void execute(Runnable command) {
        e.execute(command);
    }
    
    public void shutdown() {
        e.shutdown();
    }
    
    public List shutdownNow() {
        return e.shutdownNow();
    }
    
    public boolean isShutdown() {
        return e.isShutdown();
    }
    
    public boolean isTerminated() {
        return e.isTerminated();
    }
    
    public boolean awaitTermination(long timeout, TimeUnit unit) throws InterruptedException {
        return e.awaitTermination(timeout, unit);
    }
    
    public Future submit(Runnable task) {
        return e.submit(task);
    }
    
    public Future submit(Callable task) {
        return e.submit(task);
    }
    
    public Future submit(Runnable task, Object result) {
        return e.submit(task, result);
    }
    
    public List invokeAll(Collection tasks) throws InterruptedException {
        return e.invokeAll(tasks);
    }
    
    public List invokeAll(Collection tasks, long timeout, TimeUnit unit) throws InterruptedException {
        return e.invokeAll(tasks, timeout, unit);
    }
    
    public Object invokeAny(Collection tasks) throws InterruptedException, ExecutionException {
        return e.invokeAny(tasks);
    }
    
    public Object invokeAny(Collection tasks, long timeout, TimeUnit unit) throws InterruptedException, ExecutionException, TimeoutException {
        return e.invokeAny(tasks, timeout, unit);
    }
}
