package javax.management;

public interface NotificationFilter extends java.io.Serializable {
    
    public boolean isNotificationEnabled(Notification notification);
}
