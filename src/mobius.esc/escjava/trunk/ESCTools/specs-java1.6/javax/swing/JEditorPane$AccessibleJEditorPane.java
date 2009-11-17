package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.net.*;
import java.util.*;
import java.io.*;
import java.util.*;
import javax.swing.plaf.*;
import javax.swing.text.*;
import javax.swing.event.*;
import javax.swing.text.html.*;
import javax.accessibility.*;

public class JEditorPane$AccessibleJEditorPane extends JTextComponent$AccessibleJTextComponent {
    /*synthetic*/ final JEditorPane this$0;
    
    protected JEditorPane$AccessibleJEditorPane(/*synthetic*/ final JEditorPane this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public String getAccessibleDescription() {
        if (accessibleDescription != null) {
            return accessibleDescription;
        } else {
            return this$0.getContentType();
        }
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        states.add(AccessibleState.MULTI_LINE);
        return states;
    }
}
