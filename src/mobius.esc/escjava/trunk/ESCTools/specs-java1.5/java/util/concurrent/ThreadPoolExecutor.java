package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

public class ThreadPoolExecutor extends AbstractExecutorService {
    /*synthetic*/ static final boolean $assertionsDisabled = !ThreadPoolExecutor.class.desiredAssertionStatus();
    private static final Runnable[] EMPTY_RUNNABLE_ARRAY = new Runnable[0];
    private static final RuntimePermission shutdownPerm = new RuntimePermission("modifyThread");
    private final BlockingQueue workQueue;
    private final ReentrantLock mainLock = new ReentrantLock();
    private final Condition termination = mainLock.newCondition();
    private final HashSet workers = new HashSet();
    private volatile long keepAliveTime;
    private volatile int corePoolSize;
    private volatile int maximumPoolSize;
    private volatile int poolSize;
    volatile int runState;
    static final int RUNNING = 0;
    static final int SHUTDOWN = 1;
    static final int STOP = 2;
    static final int TERMINATED = 3;
    private volatile RejectedExecutionHandler handler;
    private volatile ThreadFactory threadFactory;
    private int largestPoolSize;
    private long completedTaskCount;
    private static final RejectedExecutionHandler defaultHandler = new ThreadPoolExecutor$AbortPolicy();
    
    void reject(Runnable command) {
        handler.rejectedExecution(command, this);
    }
    
    private Thread addThread(Runnable firstTask) {
        ThreadPoolExecutor$Worker w = new ThreadPoolExecutor$Worker(this, firstTask);
        Thread t = threadFactory.newThread(w);
        if (t != null) {
            w.thread = t;
            workers.add(w);
            int nt = ++poolSize;
            if (nt > largestPoolSize) largestPoolSize = nt;
        }
        return t;
    }
    
    private boolean addIfUnderCorePoolSize(Runnable firstTask) {
        Thread t = null;
        final ReentrantLock mainLock = this.mainLock;
        mainLock.lock();
        try {
            if (poolSize < corePoolSize) t = addThread(firstTask);
        } finally {
            mainLock.unlock();
        }
        if (t == null) return false;
        t.start();
        return true;
    }
    
    private Runnable addIfUnderMaximumPoolSize(Runnable firstTask) {
        Thread t = null;
        Runnable next = null;
        final ReentrantLock mainLock = this.mainLock;
        mainLock.lock();
        try {
            if (poolSize < maximumPoolSize) {
                next = (Runnable)workQueue.poll();
                if (next == null) next = firstTask;
                t = addThread(next);
            }
        } finally {
            mainLock.unlock();
        }
        if (t == null) return null;
        t.start();
        return next;
    }
    
    Runnable getTask() throws InterruptedException {
        for (; ; ) {
            switch (runState) {
            case RUNNING: 
                {
                    if (poolSize <= corePoolSize) return (Runnable)workQueue.take();
                    long timeout = keepAliveTime;
                    if (timeout <= 0) return null;
                    Runnable r = (Runnable)workQueue.poll(timeout, TimeUnit.NANOSECONDS);
                    if (r != null) return r;
                    if (poolSize > corePoolSize) return null;
                    break;
                }
            
            case SHUTDOWN: 
                {
                    Runnable r = (Runnable)workQueue.poll();
                    if (r != null) return r;
                    if (workQueue.isEmpty()) {
                        interruptIdleWorkers();
                        return null;
                    }
                    try {
                        return (Runnable)workQueue.take();
                    } catch (InterruptedException ignore) {
                    }
                    break;
                }
            
            case STOP: 
                return null;
            
            default: 
                if (!$assertionsDisabled) throw new AssertionError();
            
            }
        }
    }
    
    void interruptIdleWorkers() {
        final ReentrantLock mainLock = this.mainLock;
        mainLock.lock();
        try {
            for (Iterator i$ = workers.iterator(); i$.hasNext(); ) {
                ThreadPoolExecutor$Worker w = (ThreadPoolExecutor$Worker)i$.next();
                w.interruptIfIdle();
            }
        } finally {
            mainLock.unlock();
        }
    }
    
    void workerDone(ThreadPoolExecutor$Worker w) {
        final ReentrantLock mainLock = this.mainLock;
        mainLock.lock();
        try {
            completedTaskCount += w.completedTasks;
            workers.remove(w);
            if (--poolSize > 0) return;
            int state = runState;
            if (!$assertionsDisabled && !(state != TERMINATED)) throw new AssertionError();
            if (state != STOP) {
                if (!workQueue.isEmpty()) {
                    Thread t = addThread(null);
                    if (t != null) t.start();
                    return;
                }
                if (state == RUNNING) return;
            }
            termination.signalAll();
            runState = TERMINATED;
        } finally {
            mainLock.unlock();
        }
        if (!$assertionsDisabled && !(runState == TERMINATED)) throw new AssertionError();
        terminated();
    }
    {
    }
    
    public ThreadPoolExecutor(int corePoolSize, int maximumPoolSize, long keepAliveTime, TimeUnit unit, BlockingQueue workQueue) {
        this(corePoolSize, maximumPoolSize, keepAliveTime, unit, workQueue, Executors.defaultThreadFactory(), defaultHandler);
    }
    
    public ThreadPoolExecutor(int corePoolSize, int maximumPoolSize, long keepAliveTime, TimeUnit unit, BlockingQueue workQueue, ThreadFactory threadFactory) {
        this(corePoolSize, maximumPoolSize, keepAliveTime, unit, workQueue, threadFactory, defaultHandler);
    }
    
    public ThreadPoolExecutor(int corePoolSize, int maximumPoolSize, long keepAliveTime, TimeUnit unit, BlockingQueue workQueue, RejectedExecutionHandler handler) {
        this(corePoolSize, maximumPoolSize, keepAliveTime, unit, workQueue, Executors.defaultThreadFactory(), handler);
    }
    
    public ThreadPoolExecutor(int corePoolSize, int maximumPoolSize, long keepAliveTime, TimeUnit unit, BlockingQueue workQueue, ThreadFactory threadFactory, RejectedExecutionHandler handler) {
        
        if (corePoolSize < 0 || maximumPoolSize <= 0 || maximumPoolSize < corePoolSize || keepAliveTime < 0) throw new IllegalArgumentException();
        if (workQueue == null || threadFactory == null || handler == null) throw new NullPointerException();
        this.corePoolSize = corePoolSize;
        this.maximumPoolSize = maximumPoolSize;
        this.workQueue = workQueue;
        this.keepAliveTime = unit.toNanos(keepAliveTime);
        this.threadFactory = threadFactory;
        this.handler = handler;
    }
    
    public void execute(Runnable command) {
        if (command == null) throw new NullPointerException();
        for (; ; ) {
            if (runState != RUNNING) {
                reject(command);
                return;
            }
            if (poolSize < corePoolSize && addIfUnderCorePoolSize(command)) return;
            if (workQueue.offer(command)) return;
            Runnable r = addIfUnderMaximumPoolSize(command);
            if (r == command) return;
            if (r == null) {
                reject(command);
                return;
            }
        }
    }
    
    public void shutdown() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) java.security.AccessController.checkPermission(shutdownPerm);
        boolean fullyTerminated = false;
        final ReentrantLock mainLock = this.mainLock;
        mainLock.lock();
        try {
            if (workers.size() > 0) {
                if (security != null) {
                    for (Iterator i$ = workers.iterator(); i$.hasNext(); ) {
                        ThreadPoolExecutor$Worker w = (ThreadPoolExecutor$Worker)i$.next();
                        security.checkAccess(w.thread);
                    }
                }
                int state = runState;
                if (state == RUNNING) runState = SHUTDOWN;
                try {
                    for (Iterator i$ = workers.iterator(); i$.hasNext(); ) {
                        ThreadPoolExecutor$Worker w = (ThreadPoolExecutor$Worker)i$.next();
                        w.interruptIfIdle();
                    }
                } catch (SecurityException se) {
                    runState = state;
                    throw se;
                }
            } else {
                fullyTerminated = true;
                runState = TERMINATED;
                termination.signalAll();
            }
        } finally {
            mainLock.unlock();
        }
        if (fullyTerminated) terminated();
    }
    
    public List shutdownNow() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) java.security.AccessController.checkPermission(shutdownPerm);
        boolean fullyTerminated = false;
        final ReentrantLock mainLock = this.mainLock;
        mainLock.lock();
        try {
            if (workers.size() > 0) {
                if (security != null) {
                    for (Iterator i$ = workers.iterator(); i$.hasNext(); ) {
                        ThreadPoolExecutor$Worker w = (ThreadPoolExecutor$Worker)i$.next();
                        security.checkAccess(w.thread);
                    }
                }
                int state = runState;
                if (state != TERMINATED) runState = STOP;
                try {
                    for (Iterator i$ = workers.iterator(); i$.hasNext(); ) {
                        ThreadPoolExecutor$Worker w = (ThreadPoolExecutor$Worker)i$.next();
                        w.interruptNow();
                    }
                } catch (SecurityException se) {
                    runState = state;
                    throw se;
                }
            } else {
                fullyTerminated = true;
                runState = TERMINATED;
                termination.signalAll();
            }
        } finally {
            mainLock.unlock();
        }
        if (fullyTerminated) terminated();
        return Arrays.asList(workQueue.toArray(EMPTY_RUNNABLE_ARRAY));
    }
    
    public boolean isShutdown() {
        return runState != RUNNING;
    }
    
    public boolean isTerminating() {
        return runState == STOP;
    }
    
    public boolean isTerminated() {
        return runState == TERMINATED;
    }
    
    public boolean awaitTermination(long timeout, TimeUnit unit) throws InterruptedException {
        long nanos = unit.toNanos(timeout);
        final ReentrantLock mainLock = this.mainLock;
        mainLock.lock();
        try {
            for (; ; ) {
                if (runState == TERMINATED) return true;
                if (nanos <= 0) return false;
                nanos = termination.awaitNanos(nanos);
            }
        } finally {
            mainLock.unlock();
        }
    }
    
    protected void finalize() {
        shutdown();
    }
    
    public void setThreadFactory(ThreadFactory threadFactory) {
        if (threadFactory == null) throw new NullPointerException();
        this.threadFactory = threadFactory;
    }
    
    public ThreadFactory getThreadFactory() {
        return threadFactory;
    }
    
    public void setRejectedExecutionHandler(RejectedExecutionHandler handler) {
        if (handler == null) throw new NullPointerException();
        this.handler = handler;
    }
    
    public RejectedExecutionHandler getRejectedExecutionHandler() {
        return handler;
    }
    
    public BlockingQueue getQueue() {
        return workQueue;
    }
    
    public boolean remove(Runnable task) {
        return getQueue().remove(task);
    }
    
    public void purge() {
        try {
            Iterator it = getQueue().iterator();
            while (it.hasNext()) {
                Runnable r = (Runnable)it.next();
                if (r instanceof Future) {
                    Future c = (Future)(Future)r;
                    if (c.isCancelled()) it.remove();
                }
            }
        } catch (ConcurrentModificationException ex) {
            return;
        }
    }
    
    public void setCorePoolSize(int corePoolSize) {
        if (corePoolSize < 0) throw new IllegalArgumentException();
        final ReentrantLock mainLock = this.mainLock;
        mainLock.lock();
        try {
            int extra = this.corePoolSize - corePoolSize;
            this.corePoolSize = corePoolSize;
            if (extra < 0) {
                int n = workQueue.size();
                while (extra++ < 0 && n-- > 0 && poolSize < corePoolSize) {
                    Thread t = addThread(null);
                    if (t != null) t.start(); else break;
                }
            } else if (extra > 0 && poolSize > corePoolSize) {
                Iterator it = workers.iterator();
                while (it.hasNext() && extra-- > 0 && poolSize > corePoolSize && workQueue.remainingCapacity() == 0) ((ThreadPoolExecutor$Worker)it.next()).interruptIfIdle();
            }
        } finally {
            mainLock.unlock();
        }
    }
    
    public int getCorePoolSize() {
        return corePoolSize;
    }
    
    public boolean prestartCoreThread() {
        return addIfUnderCorePoolSize(null);
    }
    
    public int prestartAllCoreThreads() {
        int n = 0;
        while (addIfUnderCorePoolSize(null)) ++n;
        return n;
    }
    
    public void setMaximumPoolSize(int maximumPoolSize) {
        if (maximumPoolSize <= 0 || maximumPoolSize < corePoolSize) throw new IllegalArgumentException();
        final ReentrantLock mainLock = this.mainLock;
        mainLock.lock();
        try {
            int extra = this.maximumPoolSize - maximumPoolSize;
            this.maximumPoolSize = maximumPoolSize;
            if (extra > 0 && poolSize > maximumPoolSize) {
                Iterator it = workers.iterator();
                while (it.hasNext() && extra > 0 && poolSize > maximumPoolSize) {
                    ((ThreadPoolExecutor$Worker)it.next()).interruptIfIdle();
                    --extra;
                }
            }
        } finally {
            mainLock.unlock();
        }
    }
    
    public int getMaximumPoolSize() {
        return maximumPoolSize;
    }
    
    public void setKeepAliveTime(long time, TimeUnit unit) {
        if (time < 0) throw new IllegalArgumentException();
        this.keepAliveTime = unit.toNanos(time);
    }
    
    public long getKeepAliveTime(TimeUnit unit) {
        return unit.convert(keepAliveTime, TimeUnit.NANOSECONDS);
    }
    
    public int getPoolSize() {
        return poolSize;
    }
    
    public int getActiveCount() {
        final ReentrantLock mainLock = this.mainLock;
        mainLock.lock();
        try {
            int n = 0;
            for (Iterator i$ = workers.iterator(); i$.hasNext(); ) {
                ThreadPoolExecutor$Worker w = (ThreadPoolExecutor$Worker)i$.next();
                {
                    if (w.isActive()) ++n;
                }
            }
            return n;
        } finally {
            mainLock.unlock();
        }
    }
    
    public int getLargestPoolSize() {
        final ReentrantLock mainLock = this.mainLock;
        mainLock.lock();
        try {
            return largestPoolSize;
        } finally {
            mainLock.unlock();
        }
    }
    
    public long getTaskCount() {
        final ReentrantLock mainLock = this.mainLock;
        mainLock.lock();
        try {
            long n = completedTaskCount;
            for (Iterator i$ = workers.iterator(); i$.hasNext(); ) {
                ThreadPoolExecutor$Worker w = (ThreadPoolExecutor$Worker)i$.next();
                {
                    n += w.completedTasks;
                    if (w.isActive()) ++n;
                }
            }
            return n + workQueue.size();
        } finally {
            mainLock.unlock();
        }
    }
    
    public long getCompletedTaskCount() {
        final ReentrantLock mainLock = this.mainLock;
        mainLock.lock();
        try {
            long n = completedTaskCount;
            for (Iterator i$ = workers.iterator(); i$.hasNext(); ) {
                ThreadPoolExecutor$Worker w = (ThreadPoolExecutor$Worker)i$.next();
                n += w.completedTasks;
            }
            return n;
        } finally {
            mainLock.unlock();
        }
    }
    
    protected void beforeExecute(Thread t, Runnable r) {
    }
    
    protected void afterExecute(Runnable r, Throwable t) {
    }
    
    protected void terminated() {
    }
    {
    }
    {
    }
    {
    }
    {
    }
}
