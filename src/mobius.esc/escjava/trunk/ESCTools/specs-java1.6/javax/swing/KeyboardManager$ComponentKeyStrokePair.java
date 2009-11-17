package javax.swing;

import java.util.*;
import java.awt.*;
import java.awt.event.*;
import java.applet.*;
import java.beans.*;
import javax.swing.event.*;

class KeyboardManager$ComponentKeyStrokePair {
    /*synthetic*/ final KeyboardManager this$0;
    Object component;
    Object keyStroke;
    
    public KeyboardManager$ComponentKeyStrokePair(/*synthetic*/ final KeyboardManager this$0, Object comp, Object key) {
        this.this$0 = this$0;
        
        component = comp;
        keyStroke = key;
    }
    
    public boolean equals(Object o) {
        if (!(o instanceof KeyboardManager$ComponentKeyStrokePair)) {
            return false;
        }
        KeyboardManager$ComponentKeyStrokePair ckp = (KeyboardManager$ComponentKeyStrokePair)(KeyboardManager$ComponentKeyStrokePair)o;
        return ((component.equals(ckp.component)) && (keyStroke.equals(ckp.keyStroke)));
    }
    
    public int hashCode() {
        return component.hashCode() * keyStroke.hashCode();
    }
}
