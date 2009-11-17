package java.util.concurrent;

public interface CompletionService {
    
    Future submit(Callable task);
    
    Future submit(Runnable task, Object result);
    
    Future take() throws InterruptedException;
    
    Future poll();
    
    Future poll(long timeout, TimeUnit unit) throws InterruptedException;
}
