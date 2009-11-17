package java.lang.management;

public interface ClassLoadingMXBean {
    
    public long getTotalLoadedClassCount();
    
    public int getLoadedClassCount();
    
    public long getUnloadedClassCount();
    
    public boolean isVerbose();
    
    public void setVerbose(boolean value);
}
