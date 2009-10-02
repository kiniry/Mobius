package javax.management;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import com.sun.jmx.trace.Trace;

public class NotificationBroadcasterSupport implements NotificationEmitter {
    
    public NotificationBroadcasterSupport() {
        
    }
    
    public void addNotificationListener(NotificationListener listener, NotificationFilter filter, Object handback) {
        if (listener == null) {
            throw new IllegalArgumentException("Listener can\'t be null");
        }
        synchronized (lock) {
            List newList = new ArrayList(listenerList.size() + 1);
            newList.addAll(listenerList);
            newList.add(new NotificationBroadcasterSupport$ListenerInfo(this, listener, filter, handback));
            listenerList = newList;
        }
    }
    
    public void removeNotificationListener(NotificationListener listener) throws ListenerNotFoundException {
        synchronized (lock) {
            List newList = new ArrayList(listenerList);
            for (int i = newList.size() - 1; i >= 0; i--) {
                NotificationBroadcasterSupport$ListenerInfo li = (NotificationBroadcasterSupport$ListenerInfo)(NotificationBroadcasterSupport$ListenerInfo)newList.get(i);
                if (li.listener == listener) newList.remove(i);
            }
            if (newList.size() == listenerList.size()) throw new ListenerNotFoundException("Listener not registered");
            listenerList = newList;
        }
    }
    
    public void removeNotificationListener(NotificationListener listener, NotificationFilter filter, Object handback) throws ListenerNotFoundException {
        boolean found = false;
        synchronized (lock) {
            List newList = new ArrayList(listenerList);
            final int size = newList.size();
            for (int i = 0; i < size; i++) {
                NotificationBroadcasterSupport$ListenerInfo li = (NotificationBroadcasterSupport$ListenerInfo)(NotificationBroadcasterSupport$ListenerInfo)newList.get(i);
                if (li.listener == listener) {
                    found = true;
                    if (li.filter == filter && li.handback == handback) {
                        newList.remove(i);
                        listenerList = newList;
                        return;
                    }
                }
            }
        }
        if (found) {
            throw new ListenerNotFoundException("Listener not registered with this filter and handback");
        } else {
            throw new ListenerNotFoundException("Listener not registered");
        }
    }
    
    public MBeanNotificationInfo[] getNotificationInfo() {
        return new MBeanNotificationInfo[0];
    }
    
    public void sendNotification(Notification notification) {
        if (notification == null) {
            return;
        }
        List currentList;
        synchronized (lock) {
            currentList = listenerList;
        }
        final int size = currentList.size();
        for (int i = 0; i < size; i++) {
            NotificationBroadcasterSupport$ListenerInfo li = (NotificationBroadcasterSupport$ListenerInfo)(NotificationBroadcasterSupport$ListenerInfo)currentList.get(i);
            if (li.filter == null || li.filter.isNotificationEnabled(notification)) {
                try {
                    this.handleNotification(li.listener, notification, li.handback);
                } catch (Exception e) {
                    trace("sendNotification", "exception from listener: " + e);
                }
            }
        }
    }
    
    protected void handleNotification(NotificationListener listener, Notification notif, Object handback) {
        listener.handleNotification(notif, handback);
    }
    
    private static void trace(String method, String message) {
        if (Trace.isSelected(Trace.LEVEL_TRACE, Trace.INFO_MISC)) {
            Trace.send(Trace.LEVEL_TRACE, Trace.INFO_MISC, NotificationBroadcasterSupport.class.getName(), method, message);
        }
    }
    {
    }
    private List listenerList = Collections.EMPTY_LIST;
    private final Object lock = new Object();
}
