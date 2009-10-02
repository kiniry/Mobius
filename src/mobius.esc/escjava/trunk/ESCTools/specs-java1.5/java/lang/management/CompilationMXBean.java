package java.lang.management;

public interface CompilationMXBean {
    
    public java.lang.String getName();
    
    public boolean isCompilationTimeMonitoringSupported();
    
    public long getTotalCompilationTime();
}
