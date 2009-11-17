package java.util.prefs;

import java.util.*;
import java.io.*;

class AbstractPreferences$EventDispatchThread extends Thread {
    
    /*synthetic*/ AbstractPreferences$EventDispatchThread(java.util.prefs.AbstractPreferences$1 x0) {
        this();
    }
    
    private AbstractPreferences$EventDispatchThread() {
        
    }
    
    public void run() {
        while (true) {
            EventObject event = null;
            synchronized (AbstractPreferences.access$100()) {
                try {
                    while (AbstractPreferences.access$100().isEmpty()) AbstractPreferences.access$100().wait();
                    event = (EventObject)(EventObject)AbstractPreferences.access$100().remove(0);
                } catch (InterruptedException e) {
                    return;
                }
            }
            AbstractPreferences src = (AbstractPreferences)(AbstractPreferences)event.getSource();
            if (event instanceof PreferenceChangeEvent) {
                PreferenceChangeEvent pce = (PreferenceChangeEvent)(PreferenceChangeEvent)event;
                PreferenceChangeListener[] listeners = src.prefListeners();
                for (int i = 0; i < listeners.length; i++) listeners[i].preferenceChange(pce);
            } else {
                NodeChangeEvent nce = (NodeChangeEvent)(NodeChangeEvent)event;
                NodeChangeListener[] listeners = src.nodeListeners();
                if (nce instanceof AbstractPreferences$NodeAddedEvent) {
                    for (int i = 0; i < listeners.length; i++) listeners[i].childAdded(nce);
                } else {
                    for (int i = 0; i < listeners.length; i++) listeners[i].childRemoved(nce);
                }
            }
        }
    }
}
