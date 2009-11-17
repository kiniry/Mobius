package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.util.*;

class SystemEventQueueUtilities$ComponentWorkRequest implements Runnable {
    boolean isPending;
    Component component;
    
    SystemEventQueueUtilities$ComponentWorkRequest(Component c) {
        
    }
    
    public void run() {
        RepaintManager rm;
        synchronized (this) {
            rm = RepaintManager.currentManager(component);
            isPending = false;
        }
        rm.validateInvalidComponents();
        rm.paintDirtyRegions();
    }
}
