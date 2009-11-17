package javax.management;

class NotificationBroadcasterSupport$ListenerInfo {
    /*synthetic*/ final NotificationBroadcasterSupport this$0;
    public NotificationListener listener;
    NotificationFilter filter;
    Object handback;
    
    public NotificationBroadcasterSupport$ListenerInfo(/*synthetic*/ final NotificationBroadcasterSupport this$0, NotificationListener listener, NotificationFilter filter, Object handback) {
        this.this$0 = this$0;
        
        this.listener = listener;
        this.filter = filter;
        this.handback = handback;
    }
}
