package com.sun.jmx.mbeanserver;

import java.security.PrivilegedExceptionAction;
import javax.management.NotCompliantMBeanException;
import javax.management.MBeanRegistrationException;
import javax.management.InstanceAlreadyExistsException;

class JmxMBeanServer$1 implements PrivilegedExceptionAction {
    /*synthetic*/ final JmxMBeanServer this$0;
    
    JmxMBeanServer$1(/*synthetic*/ final JmxMBeanServer this$0) throws NotCompliantMBeanException, MBeanRegistrationException, InstanceAlreadyExistsException {
        this.this$0 = this$0;
        
    }
    
    public Object run() throws Exception {
        JmxMBeanServer.access$200(this$0).registerMBean(JmxMBeanServer.access$000(this$0), JmxMBeanServer.access$100(this$0));
        return null;
    }
}
