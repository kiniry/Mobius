package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.util.*;

class SystemEventQueueUtilities$SystemEventQueue {
    
    private SystemEventQueueUtilities$SystemEventQueue() {
        
    }
    
    static EventQueue get() {
        EventQueue retValue;
        try {
            retValue = Toolkit.getDefaultToolkit().getSystemEventQueue();
        } catch (SecurityException se) {
            retValue = null;
        }
        return retValue;
    }
    
    static EventQueue get(JRootPane rootPane) {
        return get();
    }
}
