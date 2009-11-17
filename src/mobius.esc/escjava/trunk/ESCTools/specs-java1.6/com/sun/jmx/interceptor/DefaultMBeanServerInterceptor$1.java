package com.sun.jmx.interceptor;

import java.security.PrivilegedAction;
import javax.management.*;

class DefaultMBeanServerInterceptor$1 implements PrivilegedAction {
    /*synthetic*/ final Class val$theClass;
    
    DefaultMBeanServerInterceptor$1(/*synthetic*/ final Class val$theClass) {
        this.val$theClass = val$theClass;
        
    }
    
    public Object run() {
        return val$theClass.getProtectionDomain();
    }
}
