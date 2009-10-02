package java.awt;

class EventQueueItem {
    AWTEvent event;
    int id;
    EventQueueItem next;
    
    EventQueueItem(AWTEvent evt) {
        
        event = evt;
        id = evt.getID();
    }
}
