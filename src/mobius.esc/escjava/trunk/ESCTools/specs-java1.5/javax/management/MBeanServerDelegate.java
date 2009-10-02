package javax.management;

import com.sun.jmx.defaults.ServiceName;

public class MBeanServerDelegate implements MBeanServerDelegateMBean, NotificationEmitter {
    private String mbeanServerId;
    private final NotificationBroadcasterSupport broadcaster;
    private static long oldStamp = 0;
    private final long stamp;
    private long sequenceNumber = 1;
    private static final MBeanNotificationInfo[] notifsInfo;
    static {
        final String[] types = {MBeanServerNotification.UNREGISTRATION_NOTIFICATION, MBeanServerNotification.REGISTRATION_NOTIFICATION};
        notifsInfo = new MBeanNotificationInfo[1];
        notifsInfo[0] = new MBeanNotificationInfo(types, "javax.management.MBeanServerNotification", "Notifications sent by the MBeanServerDelegate MBean");
    }
    
    public MBeanServerDelegate() {
        
        stamp = getStamp();
        broadcaster = new NotificationBroadcasterSupport();
    }
    
    public synchronized String getMBeanServerId() {
        if (mbeanServerId == null) {
            String localHost;
            try {
                localHost = java.net.InetAddress.getLocalHost().getHostName();
            } catch (java.net.UnknownHostException e) {
                localHost = "localhost";
            }
            mbeanServerId = new String(localHost + "_" + stamp);
        }
        return mbeanServerId;
    }
    
    public String getSpecificationName() {
        return ServiceName.JMX_SPEC_NAME;
    }
    
    public String getSpecificationVersion() {
        return ServiceName.JMX_SPEC_VERSION;
    }
    
    public String getSpecificationVendor() {
        return ServiceName.JMX_SPEC_VENDOR;
    }
    
    public String getImplementationName() {
        return ServiceName.JMX_IMPL_NAME;
    }
    
    public String getImplementationVersion() {
        try {
            return System.getProperty("java.runtime.version");
        } catch (SecurityException e) {
            return "";
        }
    }
    
    public String getImplementationVendor() {
        return ServiceName.JMX_IMPL_VENDOR;
    }
    
    public MBeanNotificationInfo[] getNotificationInfo() {
        final int len = MBeanServerDelegate.notifsInfo.length;
        final MBeanNotificationInfo[] infos = new MBeanNotificationInfo[len];
        System.arraycopy(MBeanServerDelegate.notifsInfo, 0, infos, 0, len);
        return infos;
    }
    
    public synchronized void addNotificationListener(NotificationListener listener, NotificationFilter filter, Object handback) throws IllegalArgumentException {
        broadcaster.addNotificationListener(listener, filter, handback);
    }
    
    public synchronized void removeNotificationListener(NotificationListener listener, NotificationFilter filter, Object handback) throws ListenerNotFoundException {
        broadcaster.removeNotificationListener(listener, filter, handback);
    }
    
    public synchronized void removeNotificationListener(NotificationListener listener) throws ListenerNotFoundException {
        broadcaster.removeNotificationListener(listener);
    }
    
    public void sendNotification(Notification notification) {
        if (notification.getSequenceNumber() < 1) {
            synchronized (this) {
                notification.setSequenceNumber(this.sequenceNumber++);
            }
        }
        broadcaster.sendNotification(notification);
    }
    
    private static synchronized long getStamp() {
        long s = System.currentTimeMillis();
        if (oldStamp >= s) {
            s = oldStamp + 1;
        }
        oldStamp = s;
        return s;
    }
}
