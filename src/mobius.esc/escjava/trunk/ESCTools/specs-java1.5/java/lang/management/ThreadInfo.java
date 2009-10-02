package java.lang.management;

import javax.management.openmbean.CompositeData;
import sun.management.ThreadInfoCompositeData;

public class ThreadInfo {
    private final String threadName;
    private final long threadId;
    private final long blockedTime;
    private final long blockedCount;
    private final long waitedTime;
    private final long waitedCount;
    private final String lockName;
    private final long lockOwnerId;
    private final String lockOwnerName;
    private final boolean inNative;
    private final boolean suspended;
    private final Thread$State threadState;
    private final StackTraceElement[] stackTrace;
    
    private ThreadInfo(Thread t, int state, Object lockObj, Thread lockOwner, long blockedCount, long blockedTime, long waitedCount, long waitedTime, StackTraceElement[] stackTrace) {
        
        this.threadId = t.getId();
        this.threadName = t.getName();
        this.threadState = sun.management.ManagementFactory.toThreadState(state);
        this.suspended = sun.management.ManagementFactory.isThreadSuspended(state);
        this.inNative = sun.management.ManagementFactory.isThreadRunningNative(state);
        this.blockedCount = blockedCount;
        this.blockedTime = blockedTime;
        this.waitedCount = waitedCount;
        this.waitedTime = waitedTime;
        if (lockObj == null) {
            this.lockName = null;
        } else {
            this.lockName = lockObj.getClass().getName() + '@' + Integer.toHexString(System.identityHashCode(lockObj));
        }
        if (lockOwner == null) {
            this.lockOwnerId = -1;
            this.lockOwnerName = null;
        } else {
            ;
            this.lockOwnerId = lockOwner.getId();
            this.lockOwnerName = lockOwner.getName();
        }
        this.stackTrace = stackTrace;
    }
    
    private ThreadInfo(CompositeData cd) {
        
        ThreadInfoCompositeData.validateCompositeData(cd);
        threadId = ThreadInfoCompositeData.getThreadId(cd);
        threadName = ThreadInfoCompositeData.getThreadName(cd);
        blockedTime = ThreadInfoCompositeData.getBlockedTime(cd);
        blockedCount = ThreadInfoCompositeData.getBlockedCount(cd);
        waitedTime = ThreadInfoCompositeData.getWaitedTime(cd);
        waitedCount = ThreadInfoCompositeData.getWaitedCount(cd);
        lockName = ThreadInfoCompositeData.getLockName(cd);
        lockOwnerId = ThreadInfoCompositeData.getLockOwnerId(cd);
        lockOwnerName = ThreadInfoCompositeData.getLockOwnerName(cd);
        threadState = ThreadInfoCompositeData.getThreadState(cd);
        suspended = ThreadInfoCompositeData.isSuspended(cd);
        inNative = ThreadInfoCompositeData.isInNative(cd);
        stackTrace = ThreadInfoCompositeData.getStackTrace(cd);
    }
    
    public long getThreadId() {
        return threadId;
    }
    
    public String getThreadName() {
        return threadName;
    }
    
    public Thread$State getThreadState() {
        return threadState;
    }
    
    public long getBlockedTime() {
        return blockedTime;
    }
    
    public long getBlockedCount() {
        return blockedCount;
    }
    
    public long getWaitedTime() {
        return waitedTime;
    }
    
    public long getWaitedCount() {
        return waitedCount;
    }
    
    public String getLockName() {
        return lockName;
    }
    
    public long getLockOwnerId() {
        return lockOwnerId;
    }
    
    public String getLockOwnerName() {
        return lockOwnerName;
    }
    
    public StackTraceElement[] getStackTrace() {
        if (stackTrace == null) {
            return NO_STACK_TRACE;
        } else {
            return stackTrace;
        }
    }
    
    public boolean isSuspended() {
        return suspended;
    }
    
    public boolean isInNative() {
        return inNative;
    }
    
    public String toString() {
        return "Thread " + getThreadName() + " (Id = " + getThreadId() + ") " + getThreadState() + " " + getLockName();
    }
    
    public static ThreadInfo from(CompositeData cd) {
        if (cd == null) {
            return null;
        }
        if (cd instanceof ThreadInfoCompositeData) {
            return ((ThreadInfoCompositeData)(ThreadInfoCompositeData)cd).getThreadInfo();
        } else {
            return new ThreadInfo(cd);
        }
    }
    private static final StackTraceElement[] NO_STACK_TRACE = new StackTraceElement[0];
}
