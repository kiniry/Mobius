package java.awt;

import java.beans.*;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.logging.*;
import java.lang.reflect.*;

final class KeyboardFocusManager$HeavyweightFocusRequest {
    final Component heavyweight;
    final LinkedList lightweightRequests;
    static final KeyboardFocusManager$HeavyweightFocusRequest CLEAR_GLOBAL_FOCUS_OWNER = new KeyboardFocusManager$HeavyweightFocusRequest();
    
    private KeyboardFocusManager$HeavyweightFocusRequest() {
        
        heavyweight = null;
        lightweightRequests = null;
    }
    
    KeyboardFocusManager$HeavyweightFocusRequest(Component heavyweight, Component descendant, boolean temporary) {
        
        if (KeyboardFocusManager.access$000().on) {
            KeyboardFocusManager.access$000().assertion(heavyweight != null);
        }
        this.heavyweight = heavyweight;
        this.lightweightRequests = new LinkedList();
        addLightweightRequest(descendant, temporary);
    }
    
    boolean addLightweightRequest(Component descendant, boolean temporary) {
        if (KeyboardFocusManager.access$000().on) {
            KeyboardFocusManager.access$000().assertion(this != KeyboardFocusManager$HeavyweightFocusRequest.CLEAR_GLOBAL_FOCUS_OWNER);
            KeyboardFocusManager.access$000().assertion(descendant != null);
        }
        Component lastDescendant = ((lightweightRequests.size() > 0) ? ((KeyboardFocusManager$LightweightFocusRequest)(KeyboardFocusManager$LightweightFocusRequest)lightweightRequests.getLast()).component : null);
        if (descendant != lastDescendant) {
            lightweightRequests.add(new KeyboardFocusManager$LightweightFocusRequest(descendant, temporary));
            return true;
        } else {
            return false;
        }
    }
    
    KeyboardFocusManager$LightweightFocusRequest getFirstLightweightRequest() {
        if (this == CLEAR_GLOBAL_FOCUS_OWNER) {
            return null;
        }
        return (KeyboardFocusManager$LightweightFocusRequest)(KeyboardFocusManager$LightweightFocusRequest)lightweightRequests.getFirst();
    }
    
    public String toString() {
        boolean first = true;
        String str = "HeavyweightFocusRequest[heavweight=" + heavyweight + ",lightweightRequests=";
        if (lightweightRequests == null) {
            str += null;
        } else {
            str += "[";
            for (Iterator iter = lightweightRequests.iterator(); iter.hasNext(); ) {
                if (first) {
                    first = false;
                } else {
                    str += ",";
                }
                str += iter.next();
            }
            str += "]";
        }
        str += "]";
        return str;
    }
}
