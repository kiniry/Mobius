package java.awt.event;

import java.util.EventListener;
import java.awt.AWTEvent;

public interface AWTEventListener extends EventListener {
    
    public void eventDispatched(AWTEvent event);
}
