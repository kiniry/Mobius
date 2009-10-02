package com.sun.jmx.interceptor;

import javax.management.*;

class DefaultMBeanServerInterceptor$ListenerWrapper implements NotificationListener {
    
    DefaultMBeanServerInterceptor$ListenerWrapper(NotificationListener l, ObjectName name, Object mbean) {
        
        this.listener = l;
        this.name = name;
        this.mbean = mbean;
    }
    
    public void handleNotification(Notification notification, Object handback) {
        if (notification != null) {
            if (notification.getSource() == mbean) notification.setSource(name);
        }
        listener.handleNotification(notification, handback);
    }
    
    public boolean equals(Object o) {
        if (!(o instanceof DefaultMBeanServerInterceptor$ListenerWrapper)) return false;
        DefaultMBeanServerInterceptor$ListenerWrapper w = (DefaultMBeanServerInterceptor$ListenerWrapper)(DefaultMBeanServerInterceptor$ListenerWrapper)o;
        return (w.listener == listener && w.mbean == mbean && w.name.equals(name));
    }
    
    public int hashCode() {
        return (System.identityHashCode(listener) ^ System.identityHashCode(mbean));
    }
    private NotificationListener listener;
    private ObjectName name;
    private Object mbean;
}
