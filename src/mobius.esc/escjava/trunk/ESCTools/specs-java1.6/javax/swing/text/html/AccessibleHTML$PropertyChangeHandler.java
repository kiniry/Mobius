package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.accessibility.*;

class AccessibleHTML$PropertyChangeHandler implements PropertyChangeListener {
    
    /*synthetic*/ AccessibleHTML$PropertyChangeHandler(AccessibleHTML x0, javax.swing.text.html.AccessibleHTML$1 x1) {
        this(x0);
    }
    /*synthetic*/ final AccessibleHTML this$0;
    
    private AccessibleHTML$PropertyChangeHandler(/*synthetic*/ final AccessibleHTML this$0) {
        this.this$0 = this$0;
        
    }
    
    public void propertyChange(PropertyChangeEvent evt) {
        if (evt.getPropertyName().equals("document")) {
            AccessibleHTML.access$1900(this$0, AccessibleHTML.access$300(this$0).getDocument());
        }
    }
}
