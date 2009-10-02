package com.sun.jmx.mbeanserver;

import javax.management.MBeanServer;
import javax.management.MBeanServerDelegate;
import com.sun.jmx.interceptor.MBeanServerInterceptor;

public interface SunJmxMBeanServer extends MBeanServerInterceptor, MBeanServer {
    
    public MBeanInstantiator getMBeanInstantiator();
    
    public MetaData getMetaData();
    
    public boolean interceptorsEnabled();
    
    public MBeanServerInterceptor getMBeanServerInterceptor();
    
    public void setMBeanServerInterceptor(MBeanServerInterceptor interceptor);
    
    public MBeanServerDelegate getMBeanServerDelegate();
}
