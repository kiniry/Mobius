package java.util.concurrent;

public class ExecutorCompletionService implements CompletionService {
    
    /*synthetic*/ static BlockingQueue access$000(ExecutorCompletionService x0) {
        return x0.completionQueue;
    }
    private final Executor executor;
    private final BlockingQueue completionQueue;
    {
    }
    
    public ExecutorCompletionService(Executor executor) {
        
        if (executor == null) throw new NullPointerException();
        this.executor = executor;
        this.completionQueue = new LinkedBlockingQueue();
    }
    
    public ExecutorCompletionService(Executor executor, BlockingQueue completionQueue) {
        
        if (executor == null || completionQueue == null) throw new NullPointerException();
        this.executor = executor;
        this.completionQueue = completionQueue;
    }
    
    public Future submit(Callable task) {
        if (task == null) throw new NullPointerException();
        ExecutorCompletionService$QueueingFuture f = new ExecutorCompletionService$QueueingFuture(this, task);
        executor.execute(f);
        return f;
    }
    
    public Future submit(Runnable task, Object result) {
        if (task == null) throw new NullPointerException();
        ExecutorCompletionService$QueueingFuture f = new ExecutorCompletionService$QueueingFuture(this, task, result);
        executor.execute(f);
        return f;
    }
    
    public Future take() throws InterruptedException {
        return (Future)completionQueue.take();
    }
    
    public Future poll() {
        return (Future)completionQueue.poll();
    }
    
    public Future poll(long timeout, TimeUnit unit) throws InterruptedException {
        return (Future)completionQueue.poll(timeout, unit);
    }
}
