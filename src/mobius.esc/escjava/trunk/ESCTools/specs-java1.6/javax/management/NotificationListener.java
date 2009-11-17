package javax.management;

public interface NotificationListener extends java.util.EventListener {
    
    public void handleNotification(Notification notification, Object handback);
}
