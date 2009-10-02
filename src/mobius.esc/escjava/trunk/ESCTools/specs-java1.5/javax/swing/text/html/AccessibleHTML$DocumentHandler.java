package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.accessibility.*;

class AccessibleHTML$DocumentHandler implements DocumentListener {
    
    /*synthetic*/ AccessibleHTML$DocumentHandler(AccessibleHTML x0, javax.swing.text.html.AccessibleHTML$1 x1) {
        this(x0);
    }
    /*synthetic*/ final AccessibleHTML this$0;
    
    private AccessibleHTML$DocumentHandler(/*synthetic*/ final AccessibleHTML this$0) {
        this.this$0 = this$0;
        
    }
    
    public void insertUpdate(DocumentEvent e) {
        AccessibleHTML.ElementInfo.access$1800(AccessibleHTML.access$1700(this$0), e);
    }
    
    public void removeUpdate(DocumentEvent e) {
        AccessibleHTML.ElementInfo.access$1800(AccessibleHTML.access$1700(this$0), e);
    }
    
    public void changedUpdate(DocumentEvent e) {
        AccessibleHTML.ElementInfo.access$1800(AccessibleHTML.access$1700(this$0), e);
    }
}
