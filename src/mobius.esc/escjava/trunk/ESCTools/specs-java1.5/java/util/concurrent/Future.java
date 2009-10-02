package java.util.concurrent;

public interface Future {
    
    boolean cancel(boolean mayInterruptIfRunning);
    
    boolean isCancelled();
    
    boolean isDone();
    
    Object get() throws InterruptedException, ExecutionException;
    
    Object get(long timeout, TimeUnit unit) throws InterruptedException, ExecutionException, TimeoutException;
}
