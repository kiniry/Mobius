package java.util.concurrent;

import java.util.*;

public abstract class AbstractExecutorService implements ExecutorService {
    /*synthetic*/ static final boolean $assertionsDisabled = !AbstractExecutorService.class.desiredAssertionStatus();
    
    public AbstractExecutorService() {
        
    }
    
    public Future submit(Runnable task) {
        if (task == null) throw new NullPointerException();
        FutureTask ftask = new FutureTask(task, null);
        execute(ftask);
        return ftask;
    }
    
    public Future submit(Runnable task, Object result) {
        if (task == null) throw new NullPointerException();
        FutureTask ftask = new FutureTask(task, result);
        execute(ftask);
        return ftask;
    }
    
    public Future submit(Callable task) {
        if (task == null) throw new NullPointerException();
        FutureTask ftask = new FutureTask(task);
        execute(ftask);
        return ftask;
    }
    
    private Object doInvokeAny(Collection tasks, boolean timed, long nanos) throws InterruptedException, ExecutionException, TimeoutException {
        if (tasks == null) throw new NullPointerException();
        int ntasks = tasks.size();
        if (ntasks == 0) throw new IllegalArgumentException();
        List futures = new ArrayList(ntasks);
        ExecutorCompletionService ecs = new ExecutorCompletionService(this);
        try {
            ExecutionException ee = null;
            long lastTime = (timed) ? System.nanoTime() : 0;
            Iterator it = tasks.iterator();
            futures.add(ecs.submit((Callable)it.next()));
            --ntasks;
            int active = 1;
            for (; ; ) {
                Future f = ecs.poll();
                if (f == null) {
                    if (ntasks > 0) {
                        --ntasks;
                        futures.add(ecs.submit((Callable)it.next()));
                        ++active;
                    } else if (active == 0) break; else if (timed) {
                        f = ecs.poll(nanos, TimeUnit.NANOSECONDS);
                        if (f == null) throw new TimeoutException();
                        long now = System.nanoTime();
                        nanos -= now - lastTime;
                        lastTime = now;
                    } else f = ecs.take();
                }
                if (f != null) {
                    --active;
                    try {
                        return f.get();
                    } catch (InterruptedException ie) {
                        throw ie;
                    } catch (ExecutionException eex) {
                        ee = eex;
                    } catch (RuntimeException rex) {
                        ee = new ExecutionException(rex);
                    }
                }
            }
            if (ee == null) ee = new ExecutionException();
            throw ee;
        } finally {
            for (Iterator i$ = futures.iterator(); i$.hasNext(); ) {
                Future f = (Future)i$.next();
                f.cancel(true);
            }
        }
    }
    
    public Object invokeAny(Collection tasks) throws InterruptedException, ExecutionException {
        try {
            return doInvokeAny(tasks, false, 0);
        } catch (TimeoutException cannotHappen) {
            if (!$assertionsDisabled) throw new AssertionError();
            return null;
        }
    }
    
    public Object invokeAny(Collection tasks, long timeout, TimeUnit unit) throws InterruptedException, ExecutionException, TimeoutException {
        return doInvokeAny(tasks, true, unit.toNanos(timeout));
    }
    
    public List invokeAll(Collection tasks) throws InterruptedException {
        if (tasks == null) throw new NullPointerException();
        List futures = new ArrayList(tasks.size());
        boolean done = false;
        try {
            for (Iterator i$ = tasks.iterator(); i$.hasNext(); ) {
                Callable t = (Callable)i$.next();
                {
                    FutureTask f = new FutureTask(t);
                    futures.add(f);
                    execute(f);
                }
            }
            for (Iterator i$ = futures.iterator(); i$.hasNext(); ) {
                Future f = (Future)i$.next();
                {
                    if (!f.isDone()) {
                        try {
                            f.get();
                        } catch (CancellationException ignore) {
                        } catch (ExecutionException ignore) {
                        }
                    }
                }
            }
            done = true;
            return futures;
        } finally {
            if (!done) for (Iterator i$ = futures.iterator(); i$.hasNext(); ) {
                Future f = (Future)i$.next();
                f.cancel(true);
            }
        }
    }
    
    public List invokeAll(Collection tasks, long timeout, TimeUnit unit) throws InterruptedException {
        if (tasks == null || unit == null) throw new NullPointerException();
        long nanos = unit.toNanos(timeout);
        List futures = new ArrayList(tasks.size());
        boolean done = false;
        try {
            for (Iterator i$ = tasks.iterator(); i$.hasNext(); ) {
                Callable t = (Callable)i$.next();
                futures.add(new FutureTask(t));
            }
            long lastTime = System.nanoTime();
            Iterator it = futures.iterator();
            while (it.hasNext()) {
                execute((Runnable)((Runnable)it.next()));
                long now = System.nanoTime();
                nanos -= now - lastTime;
                lastTime = now;
                if (nanos <= 0) return futures;
            }
            for (Iterator i$ = futures.iterator(); i$.hasNext(); ) {
                Future f = (Future)i$.next();
                {
                    if (!f.isDone()) {
                        if (nanos <= 0) return futures;
                        try {
                            f.get(nanos, TimeUnit.NANOSECONDS);
                        } catch (CancellationException ignore) {
                        } catch (ExecutionException ignore) {
                        } catch (TimeoutException toe) {
                            return futures;
                        }
                        long now = System.nanoTime();
                        nanos -= now - lastTime;
                        lastTime = now;
                    }
                }
            }
            done = true;
            return futures;
        } finally {
            if (!done) for (Iterator i$ = futures.iterator(); i$.hasNext(); ) {
                Future f = (Future)i$.next();
                f.cancel(true);
            }
        }
    }
}
