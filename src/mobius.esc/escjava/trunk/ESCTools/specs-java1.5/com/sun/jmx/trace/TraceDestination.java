package com.sun.jmx.trace;

import java.io.IOException;

public interface TraceDestination {
    
    public boolean isSelected(int level, int type);
    
    public boolean send(int level, int type, String className, String methodName, String info);
    
    public boolean send(int level, int type, String className, String methodName, Throwable exception);
    
    public void reset() throws IOException;
}
