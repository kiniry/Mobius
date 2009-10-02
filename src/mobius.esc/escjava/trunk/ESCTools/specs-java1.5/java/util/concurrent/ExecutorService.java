package java.util.concurrent;

import java.util.List;
import java.util.Collection;

public interface ExecutorService extends Executor {
    
    void shutdown();
    
    List shutdownNow();
    
    boolean isShutdown();
    
    boolean isTerminated();
    
    boolean awaitTermination(long timeout, TimeUnit unit) throws InterruptedException;
    
    Future submit(Callable task);
    
    Future submit(Runnable task, Object result);
    
    Future submit(Runnable task);
    
    List invokeAll(Collection tasks) throws InterruptedException;
    
    List invokeAll(Collection tasks, long timeout, TimeUnit unit) throws InterruptedException;
    
    Object invokeAny(Collection tasks) throws InterruptedException, ExecutionException;
    
    Object invokeAny(Collection tasks, long timeout, TimeUnit unit) throws InterruptedException, ExecutionException, TimeoutException;
}
