package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.util.*;

class SystemEventQueueUtilities$RunnableTarget extends Component {
    
    SystemEventQueueUtilities$RunnableTarget() {
        
        enableEvents(SystemEventQueueUtilities$RunnableEvent.EVENT_ID);
    }
    
    protected void processEvent(AWTEvent event) {
        if (event instanceof SystemEventQueueUtilities$RunnableEvent) {
            SystemEventQueueUtilities.access$100((SystemEventQueueUtilities$RunnableEvent)(SystemEventQueueUtilities$RunnableEvent)event);
        }
    }
}
