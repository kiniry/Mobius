package java.lang.management;

public interface GarbageCollectorMXBean extends MemoryManagerMXBean {
    
    public long getCollectionCount();
    
    public long getCollectionTime();
}
