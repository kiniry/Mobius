package java.lang.management;

public interface RuntimeMXBean {
    
    public String getName();
    
    public String getVmName();
    
    public String getVmVendor();
    
    public String getVmVersion();
    
    public String getSpecName();
    
    public String getSpecVendor();
    
    public String getSpecVersion();
    
    public String getManagementSpecVersion();
    
    public String getClassPath();
    
    public String getLibraryPath();
    
    public boolean isBootClassPathSupported();
    
    public String getBootClassPath();
    
    public java.util.List getInputArguments();
    
    public long getUptime();
    
    public long getStartTime();
    
    public java.util.Map getSystemProperties();
}
