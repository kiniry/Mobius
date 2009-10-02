package java.awt;

class EventDispatchThread$StopDispatchEvent extends AWTEvent implements ActiveEvent {
    /*synthetic*/ final EventDispatchThread this$0;
    
    public EventDispatchThread$StopDispatchEvent(/*synthetic*/ final EventDispatchThread this$0) {
        this.this$0 = this$0;
        super(this$0, 0);
    }
    
    public void dispatch() {
        EventDispatchThread.access$002(this$0, false);
    }
}
