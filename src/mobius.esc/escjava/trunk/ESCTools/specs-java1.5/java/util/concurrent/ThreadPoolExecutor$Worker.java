package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

class ThreadPoolExecutor$Worker implements Runnable {
    /*synthetic*/ final ThreadPoolExecutor this$0;
    private final ReentrantLock runLock = new ReentrantLock();
    private Runnable firstTask;
    volatile long completedTasks;
    Thread thread;
    
    ThreadPoolExecutor$Worker(/*synthetic*/ final ThreadPoolExecutor this$0, Runnable firstTask) {
        this.this$0 = this$0;
        
        this.firstTask = firstTask;
    }
    
    boolean isActive() {
        return runLock.isLocked();
    }
    
    void interruptIfIdle() {
        final ReentrantLock runLock = this.runLock;
        if (runLock.tryLock()) {
            try {
                thread.interrupt();
            } finally {
                runLock.unlock();
            }
        }
    }
    
    void interruptNow() {
        thread.interrupt();
    }
    
    private void runTask(Runnable task) {
        final ReentrantLock runLock = this.runLock;
        runLock.lock();
        try {
            if (this$0.runState == 2) return;
            Thread.interrupted();
            boolean ran = false;
            this$0.beforeExecute(thread, task);
            try {
                task.run();
                ran = true;
                this$0.afterExecute(task, null);
                ++completedTasks;
            } catch (RuntimeException ex) {
                if (!ran) this$0.afterExecute(task, ex);
                throw ex;
            }
        } finally {
            runLock.unlock();
        }
    }
    
    public void run() {
        try {
            Runnable task = firstTask;
            firstTask = null;
            while (task != null || (task = this$0.getTask()) != null) {
                runTask(task);
                task = null;
            }
        } catch (InterruptedException ie) {
        } finally {
            this$0.workerDone(this);
        }
    }
}
