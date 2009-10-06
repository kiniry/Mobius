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

public class JEditorPane$AccessibleJEditorPaneHTML extends JEditorPane$AccessibleJEditorPane {
    /*synthetic*/ final JEditorPane this$0;
    private AccessibleContext accessibleContext;
    
    public AccessibleText getAccessibleText() {
        return new JEditorPane$JEditorPaneAccessibleHypertextSupport(this$0);
    }
    
    protected JEditorPane$AccessibleJEditorPaneHTML(/*synthetic*/ final JEditorPane this$0) {
        super(this$0);

        HTMLEditorKit kit = (HTMLEditorKit)(HTMLEditorKit)this$0.getEditorKit();
        accessibleContext = kit.getAccessibleContext();
    }
    
    public int getAccessibleChildrenCount() {
        if (accessibleContext != null) {
            return accessibleContext.getAccessibleChildrenCount();
        } else {
            return 0;
        }
    }
    
    public Accessible getAccessibleChild(int i) {
        if (accessibleContext != null) {
            return accessibleContext.getAccessibleChild(i);
        } else {
            return null;
        }
    }
    
    public Accessible getAccessibleAt(Point p) {
        if (accessibleContext != null && p != null) {
            try {
                AccessibleComponent acomp = accessibleContext.getAccessibleComponent();
                if (acomp != null) {
                    return acomp.getAccessibleAt(p);
                } else {
                    return null;
                }
            } catch (IllegalComponentStateException e) {
                return null;
            }
        } else {
            return null;
        }
    }
}
