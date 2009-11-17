package java.lang.management;

public interface ThreadMXBean {
    
    public int getThreadCount();
    
    public int getPeakThreadCount();
    
    public long getTotalStartedThreadCount();
    
    public int getDaemonThreadCount();
    
    public long[] getAllThreadIds();
    
    public ThreadInfo getThreadInfo(long id);
    
    public ThreadInfo[] getThreadInfo(long[] ids);
    
    public ThreadInfo getThreadInfo(long id, int maxDepth);
    
    public ThreadInfo[] getThreadInfo(long[] ids, int maxDepth);
    
    public boolean isThreadContentionMonitoringSupported();
    
    public boolean isThreadContentionMonitoringEnabled();
    
    public void setThreadContentionMonitoringEnabled(boolean enable);
    
    public long getCurrentThreadCpuTime();
    
    public long getCurrentThreadUserTime();
    
    public long getThreadCpuTime(long id);
    
    public long getThreadUserTime(long id);
    
    public boolean isThreadCpuTimeSupported();
    
    public boolean isCurrentThreadCpuTimeSupported();
    
    public boolean isThreadCpuTimeEnabled();
    
    public void setThreadCpuTimeEnabled(boolean enable);
    
    public long[] findMonitorDeadlockedThreads();
    
    public void resetPeakThreadCount();
}
