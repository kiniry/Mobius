package java.lang.management;

public interface MemoryManagerMXBean {
    
    public String getName();
    
    public boolean isValid();
    
    public String[] getMemoryPoolNames();
}
