package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.Serializable;

public class JTabbedPane$ModelListener implements ChangeListener, Serializable {
    /*synthetic*/ final JTabbedPane this$0;
    
    protected JTabbedPane$ModelListener(/*synthetic*/ final JTabbedPane this$0) {
        this.this$0 = this$0;
        
    }
    
    public void stateChanged(ChangeEvent e) {
        this$0.fireStateChanged();
    }
}
