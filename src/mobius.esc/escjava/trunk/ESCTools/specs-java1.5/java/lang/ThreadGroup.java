package java.lang;

import java.io.PrintStream;
import sun.misc.VM;

public class ThreadGroup implements Thread$UncaughtExceptionHandler {
    ThreadGroup parent;
    String name;
    int maxPriority;
    boolean destroyed;
    boolean daemon;
    boolean vmAllowSuspension;
    int nUnstartedThreads = 0;
    int nthreads;
    Thread[] threads;
    int ngroups;
    ThreadGroup[] groups;
    
    private ThreadGroup() {
        
        this.name = "system";
        this.maxPriority = Thread.MAX_PRIORITY;
    }
    
    public ThreadGroup(String name) {
        this(Thread.currentThread().getThreadGroup(), name);
    }
    
    public ThreadGroup(ThreadGroup parent, String name) {
        
        if (parent == null) {
            throw new NullPointerException();
        }
        parent.checkAccess();
        this.name = name;
        this.maxPriority = parent.maxPriority;
        this.daemon = parent.daemon;
        this.vmAllowSuspension = parent.vmAllowSuspension;
        this.parent = parent;
        parent.add(this);
    }
    
    public final String getName() {
        return name;
    }
    
    public final ThreadGroup getParent() {
        if (parent != null) parent.checkAccess();
        return parent;
    }
    
    public final int getMaxPriority() {
        return maxPriority;
    }
    
    public final boolean isDaemon() {
        return daemon;
    }
    
    public synchronized boolean isDestroyed() {
        return destroyed;
    }
    
    public final void setDaemon(boolean daemon) {
        checkAccess();
        this.daemon = daemon;
    }
    
    public final void setMaxPriority(int pri) {
        int ngroupsSnapshot;
        ThreadGroup[] groupsSnapshot;
        synchronized (this) {
            checkAccess();
            if (pri < Thread.MIN_PRIORITY) {
                maxPriority = Thread.MIN_PRIORITY;
            } else if (pri < maxPriority) {
                maxPriority = pri;
            }
            ngroupsSnapshot = ngroups;
            if (groups != null) {
                groupsSnapshot = new ThreadGroup[ngroupsSnapshot];
                System.arraycopy(groups, 0, groupsSnapshot, 0, ngroupsSnapshot);
            } else {
                groupsSnapshot = null;
            }
        }
        for (int i = 0; i < ngroupsSnapshot; i++) {
            groupsSnapshot[i].setMaxPriority(pri);
        }
    }
    
    public final boolean parentOf(ThreadGroup g) {
        for (; g != null; g = g.parent) {
            if (g == this) {
                return true;
            }
        }
        return false;
    }
    
    public final void checkAccess() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkAccess(this);
        }
    }
    
    public int activeCount() {
        int result;
        int ngroupsSnapshot;
        ThreadGroup[] groupsSnapshot;
        synchronized (this) {
            if (destroyed) {
                return 0;
            }
            result = nthreads;
            ngroupsSnapshot = ngroups;
            if (groups != null) {
                groupsSnapshot = new ThreadGroup[ngroupsSnapshot];
                System.arraycopy(groups, 0, groupsSnapshot, 0, ngroupsSnapshot);
            } else {
                groupsSnapshot = null;
            }
        }
        for (int i = 0; i < ngroupsSnapshot; i++) {
            result += groupsSnapshot[i].activeCount();
        }
        return result;
    }
    
    public int enumerate(Thread[] list) {
        checkAccess();
        return enumerate(list, 0, true);
    }
    
    public int enumerate(Thread[] list, boolean recurse) {
        checkAccess();
        return enumerate(list, 0, recurse);
    }
    
    private int enumerate(Thread[] list, int n, boolean recurse) {
        int ngroupsSnapshot = 0;
        ThreadGroup[] groupsSnapshot = null;
        synchronized (this) {
            if (destroyed) {
                return 0;
            }
            int nt = nthreads;
            if (nt > list.length - n) {
                nt = list.length - n;
            }
            for (int i = 0; i < nt; i++) {
                if (threads[i].isAlive()) {
                    list[n++] = threads[i];
                }
            }
            if (recurse) {
                ngroupsSnapshot = ngroups;
                if (groups != null) {
                    groupsSnapshot = new ThreadGroup[ngroupsSnapshot];
                    System.arraycopy(groups, 0, groupsSnapshot, 0, ngroupsSnapshot);
                } else {
                    groupsSnapshot = null;
                }
            }
        }
        if (recurse) {
            for (int i = 0; i < ngroupsSnapshot; i++) {
                n = groupsSnapshot[i].enumerate(list, n, true);
            }
        }
        return n;
    }
    
    public int activeGroupCount() {
        int ngroupsSnapshot;
        ThreadGroup[] groupsSnapshot;
        synchronized (this) {
            if (destroyed) {
                return 0;
            }
            ngroupsSnapshot = ngroups;
            if (groups != null) {
                groupsSnapshot = new ThreadGroup[ngroupsSnapshot];
                System.arraycopy(groups, 0, groupsSnapshot, 0, ngroupsSnapshot);
            } else {
                groupsSnapshot = null;
            }
        }
        int n = ngroupsSnapshot;
        for (int i = 0; i < ngroupsSnapshot; i++) {
            n += groupsSnapshot[i].activeGroupCount();
        }
        return n;
    }
    
    public int enumerate(ThreadGroup[] list) {
        checkAccess();
        return enumerate(list, 0, true);
    }
    
    public int enumerate(ThreadGroup[] list, boolean recurse) {
        checkAccess();
        return enumerate(list, 0, recurse);
    }
    
    private int enumerate(ThreadGroup[] list, int n, boolean recurse) {
        int ngroupsSnapshot = 0;
        ThreadGroup[] groupsSnapshot = null;
        synchronized (this) {
            if (destroyed) {
                return 0;
            }
            int ng = ngroups;
            if (ng > list.length - n) {
                ng = list.length - n;
            }
            if (ng > 0) {
                System.arraycopy(groups, 0, list, n, ng);
                n += ng;
            }
            if (recurse) {
                ngroupsSnapshot = ngroups;
                if (groups != null) {
                    groupsSnapshot = new ThreadGroup[ngroupsSnapshot];
                    System.arraycopy(groups, 0, groupsSnapshot, 0, ngroupsSnapshot);
                } else {
                    groupsSnapshot = null;
                }
            }
        }
        if (recurse) {
            for (int i = 0; i < ngroupsSnapshot; i++) {
                n = groupsSnapshot[i].enumerate(list, n, true);
            }
        }
        return n;
    }
    
    
    public final void stop() {
        if (stopOrSuspend(false)) Thread.currentThread().stop();
    }
    
    public final void interrupt() {
        int ngroupsSnapshot;
        ThreadGroup[] groupsSnapshot;
        synchronized (this) {
            checkAccess();
            for (int i = 0; i < nthreads; i++) {
                threads[i].interrupt();
            }
            ngroupsSnapshot = ngroups;
            if (groups != null) {
                groupsSnapshot = new ThreadGroup[ngroupsSnapshot];
                System.arraycopy(groups, 0, groupsSnapshot, 0, ngroupsSnapshot);
            } else {
                groupsSnapshot = null;
            }
        }
        for (int i = 0; i < ngroupsSnapshot; i++) {
            groupsSnapshot[i].interrupt();
        }
    }
    
    
    public final void suspend() {
        if (stopOrSuspend(true)) Thread.currentThread().suspend();
    }
    
    private boolean stopOrSuspend(boolean suspend) {
        boolean suicide = false;
        Thread us = Thread.currentThread();
        int ngroupsSnapshot;
        ThreadGroup[] groupsSnapshot = null;
        synchronized (this) {
            checkAccess();
            for (int i = 0; i < nthreads; i++) {
                if (threads[i] == us) suicide = true; else if (suspend) threads[i].suspend(); else threads[i].stop();
            }
            ngroupsSnapshot = ngroups;
            if (groups != null) {
                groupsSnapshot = new ThreadGroup[ngroupsSnapshot];
                System.arraycopy(groups, 0, groupsSnapshot, 0, ngroupsSnapshot);
            }
        }
        for (int i = 0; i < ngroupsSnapshot; i++) suicide = groupsSnapshot[i].stopOrSuspend(suspend) || suicide;
        return suicide;
    }
    
    
    public final void resume() {
        int ngroupsSnapshot;
        ThreadGroup[] groupsSnapshot;
        synchronized (this) {
            checkAccess();
            for (int i = 0; i < nthreads; i++) {
                threads[i].resume();
            }
            ngroupsSnapshot = ngroups;
            if (groups != null) {
                groupsSnapshot = new ThreadGroup[ngroupsSnapshot];
                System.arraycopy(groups, 0, groupsSnapshot, 0, ngroupsSnapshot);
            } else {
                groupsSnapshot = null;
            }
        }
        for (int i = 0; i < ngroupsSnapshot; i++) {
            groupsSnapshot[i].resume();
        }
    }
    
    public final void destroy() {
        int ngroupsSnapshot;
        ThreadGroup[] groupsSnapshot;
        synchronized (this) {
            checkAccess();
            if (destroyed || (nthreads > 0)) {
                throw new IllegalThreadStateException();
            }
            ngroupsSnapshot = ngroups;
            if (groups != null) {
                groupsSnapshot = new ThreadGroup[ngroupsSnapshot];
                System.arraycopy(groups, 0, groupsSnapshot, 0, ngroupsSnapshot);
            } else {
                groupsSnapshot = null;
            }
            if (parent != null) {
                destroyed = true;
                ngroups = 0;
                groups = null;
                nthreads = 0;
                threads = null;
            }
        }
        for (int i = 0; i < ngroupsSnapshot; i += 1) {
            groupsSnapshot[i].destroy();
        }
        if (parent != null) {
            parent.remove(this);
        }
    }
    
    private final void add(ThreadGroup g) {
        synchronized (this) {
            if (destroyed) {
                throw new IllegalThreadStateException();
            }
            if (groups == null) {
                groups = new ThreadGroup[4];
            } else if (ngroups == groups.length) {
                ThreadGroup[] newgroups = new ThreadGroup[ngroups * 2];
                System.arraycopy(groups, 0, newgroups, 0, ngroups);
                groups = newgroups;
            }
            groups[ngroups] = g;
            ngroups++;
        }
    }
    
    private void remove(ThreadGroup g) {
        synchronized (this) {
            if (destroyed) {
                return;
            }
            for (int i = 0; i < ngroups; i++) {
                if (groups[i] == g) {
                    ngroups -= 1;
                    System.arraycopy(groups, i + 1, groups, i, ngroups - i);
                    groups[ngroups] = null;
                    break;
                }
            }
            if (nthreads == 0) {
                notifyAll();
            }
            if (daemon && (nthreads == 0) && (nUnstartedThreads == 0) && (ngroups == 0)) {
                destroy();
            }
        }
    }
    
    void addUnstarted() {
        synchronized (this) {
            if (destroyed) {
                throw new IllegalThreadStateException();
            }
            nUnstartedThreads++;
        }
    }
    
    void add(Thread t) {
        synchronized (this) {
            if (destroyed) {
                throw new IllegalThreadStateException();
            }
            if (threads == null) {
                threads = new Thread[4];
            } else if (nthreads == threads.length) {
                Thread[] newthreads = new Thread[nthreads * 2];
                System.arraycopy(threads, 0, newthreads, 0, nthreads);
                threads = newthreads;
            }
            threads[nthreads] = t;
            nthreads++;
            nUnstartedThreads--;
        }
    }
    
    void remove(Thread t) {
        synchronized (this) {
            if (destroyed) {
                return;
            }
            for (int i = 0; i < nthreads; i++) {
                if (threads[i] == t) {
                    System.arraycopy(threads, i + 1, threads, i, --nthreads - i);
                    threads[nthreads] = null;
                    break;
                }
            }
            if (nthreads == 0) {
                notifyAll();
            }
            if (daemon && (nthreads == 0) && (nUnstartedThreads == 0) && (ngroups == 0)) {
                destroy();
            }
        }
    }
    
    public void list() {
        list(System.out, 0);
    }
    
    void list(PrintStream out, int indent) {
        int ngroupsSnapshot;
        ThreadGroup[] groupsSnapshot;
        synchronized (this) {
            for (int j = 0; j < indent; j++) {
                out.print(" ");
            }
            out.println(this);
            indent += 4;
            for (int i = 0; i < nthreads; i++) {
                for (int j = 0; j < indent; j++) {
                    out.print(" ");
                }
                out.println(threads[i]);
            }
            ngroupsSnapshot = ngroups;
            if (groups != null) {
                groupsSnapshot = new ThreadGroup[ngroupsSnapshot];
                System.arraycopy(groups, 0, groupsSnapshot, 0, ngroupsSnapshot);
            } else {
                groupsSnapshot = null;
            }
        }
        for (int i = 0; i < ngroupsSnapshot; i++) {
            groupsSnapshot[i].list(out, indent);
        }
    }
    
    public void uncaughtException(Thread t, Throwable e) {
        if (parent != null) {
            parent.uncaughtException(t, e);
        } else {
            Thread$UncaughtExceptionHandler ueh = Thread.getDefaultUncaughtExceptionHandler();
            if (ueh != null) {
                ueh.uncaughtException(t, e);
            } else if (!(e instanceof ThreadDeath)) {
                System.err.print("Exception in thread \"" + t.getName() + "\" ");
                e.printStackTrace(System.err);
            }
        }
    }
    
    
    public boolean allowThreadSuspension(boolean b) {
        this.vmAllowSuspension = b;
        if (!b) {
            VM.unsuspendSomeThreads();
        }
        return true;
    }
    
    public String toString() {
        return getClass().getName() + "[name=" + getName() + ",maxpri=" + maxPriority + "]";
    }
}
