package java.util.concurrent;

import java.util.*;
import java.security.PrivilegedAction;
import java.security.PrivilegedExceptionAction;

public class Executors {
    
    public static ExecutorService newFixedThreadPool(int nThreads) {
        return new ThreadPoolExecutor(nThreads, nThreads, 0L, TimeUnit.MILLISECONDS, new LinkedBlockingQueue());
    }
    
    public static ExecutorService newFixedThreadPool(int nThreads, ThreadFactory threadFactory) {
        return new ThreadPoolExecutor(nThreads, nThreads, 0L, TimeUnit.MILLISECONDS, new LinkedBlockingQueue(), threadFactory);
    }
    
    public static ExecutorService newSingleThreadExecutor() {
        return new Executors$DelegatedExecutorService(new ThreadPoolExecutor(1, 1, 0L, TimeUnit.MILLISECONDS, new LinkedBlockingQueue()));
    }
    
    public static ExecutorService newSingleThreadExecutor(ThreadFactory threadFactory) {
        return new Executors$DelegatedExecutorService(new ThreadPoolExecutor(1, 1, 0L, TimeUnit.MILLISECONDS, new LinkedBlockingQueue(), threadFactory));
    }
    
    public static ExecutorService newCachedThreadPool() {
        return new ThreadPoolExecutor(0, Integer.MAX_VALUE, 60L, TimeUnit.SECONDS, new SynchronousQueue());
    }
    
    public static ExecutorService newCachedThreadPool(ThreadFactory threadFactory) {
        return new ThreadPoolExecutor(0, Integer.MAX_VALUE, 60L, TimeUnit.SECONDS, new SynchronousQueue(), threadFactory);
    }
    
    public static ScheduledExecutorService newSingleThreadScheduledExecutor() {
        return new Executors$DelegatedScheduledExecutorService(new ScheduledThreadPoolExecutor(1));
    }
    
    public static ScheduledExecutorService newSingleThreadScheduledExecutor(ThreadFactory threadFactory) {
        return new Executors$DelegatedScheduledExecutorService(new ScheduledThreadPoolExecutor(1, threadFactory));
    }
    
    public static ScheduledExecutorService newScheduledThreadPool(int corePoolSize) {
        return new ScheduledThreadPoolExecutor(corePoolSize);
    }
    
    public static ScheduledExecutorService newScheduledThreadPool(int corePoolSize, ThreadFactory threadFactory) {
        return new ScheduledThreadPoolExecutor(corePoolSize, threadFactory);
    }
    
    public static ExecutorService unconfigurableExecutorService(ExecutorService executor) {
        if (executor == null) throw new NullPointerException();
        return new Executors$DelegatedExecutorService(executor);
    }
    
    public static ScheduledExecutorService unconfigurableScheduledExecutorService(ScheduledExecutorService executor) {
        if (executor == null) throw new NullPointerException();
        return new Executors$DelegatedScheduledExecutorService(executor);
    }
    
    public static ThreadFactory defaultThreadFactory() {
        return new Executors$DefaultThreadFactory();
    }
    
    public static ThreadFactory privilegedThreadFactory() {
        return new Executors$PrivilegedThreadFactory();
    }
    
    public static Callable callable(Runnable task, Object result) {
        if (task == null) throw new NullPointerException();
        return new Executors$RunnableAdapter(task, result);
    }
    
    public static Callable callable(Runnable task) {
        if (task == null) throw new NullPointerException();
        return new Executors$RunnableAdapter(task, null);
    }
    
    public static Callable callable(PrivilegedAction action) {
        if (action == null) throw new NullPointerException();
        return new Executors$PrivilegedActionAdapter(action);
    }
    
    public static Callable callable(PrivilegedExceptionAction action) {
        if (action == null) throw new NullPointerException();
        return new Executors$PrivilegedExceptionActionAdapter(action);
    }
    
    public static Callable privilegedCallable(Callable callable) {
        if (callable == null) throw new NullPointerException();
        return new Executors$PrivilegedCallable(callable);
    }
    
    public static Callable privilegedCallableUsingCurrentClassLoader(Callable callable) {
        if (callable == null) throw new NullPointerException();
        return new Executors$PrivilegedCallableUsingCurrentClassLoader(callable);
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    
    private Executors() {
        
    }
}
