package java.lang.management;

public interface MemoryMXBean {
    
    public int getObjectPendingFinalizationCount();
    
    public MemoryUsage getHeapMemoryUsage();
    
    public MemoryUsage getNonHeapMemoryUsage();
    
    public boolean isVerbose();
    
    public void setVerbose(boolean value);
    
    public void gc();
}
