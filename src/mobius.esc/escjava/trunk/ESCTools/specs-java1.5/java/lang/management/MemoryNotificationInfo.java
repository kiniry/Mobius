package java.lang.management;

import javax.management.openmbean.CompositeData;
import sun.management.MemoryNotifInfoCompositeData;

public class MemoryNotificationInfo {
    private final String poolName;
    private final MemoryUsage usage;
    private final long count;
    public static final String MEMORY_THRESHOLD_EXCEEDED = "java.management.memory.threshold.exceeded";
    public static final String MEMORY_COLLECTION_THRESHOLD_EXCEEDED = "java.management.memory.collection.threshold.exceeded";
    
    public MemoryNotificationInfo(String poolName, MemoryUsage usage, long count) {
        
        if (poolName == null) {
            throw new NullPointerException("Null poolName");
        }
        if (usage == null) {
            throw new NullPointerException("Null usage");
        }
        this.poolName = poolName;
        this.usage = usage;
        this.count = count;
    }
    
    MemoryNotificationInfo(CompositeData cd) {
        
        MemoryNotifInfoCompositeData.validateCompositeData(cd);
        this.poolName = MemoryNotifInfoCompositeData.getPoolName(cd);
        this.usage = MemoryNotifInfoCompositeData.getUsage(cd);
        this.count = MemoryNotifInfoCompositeData.getCount(cd);
    }
    
    public String getPoolName() {
        return poolName;
    }
    
    public MemoryUsage getUsage() {
        return usage;
    }
    
    public long getCount() {
        return count;
    }
    
    public static MemoryNotificationInfo from(CompositeData cd) {
        if (cd == null) {
            return null;
        }
        if (cd instanceof MemoryNotifInfoCompositeData) {
            return ((MemoryNotifInfoCompositeData)(MemoryNotifInfoCompositeData)cd).getMemoryNotifInfo();
        } else {
            return new MemoryNotificationInfo(cd);
        }
    }
}
