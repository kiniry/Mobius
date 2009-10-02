package java.lang.management;

public interface OperatingSystemMXBean {
    
    public String getName();
    
    public String getArch();
    
    public String getVersion();
    
    public int getAvailableProcessors();
}
