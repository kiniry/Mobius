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

class JEditorPane$1 extends LayoutFocusTraversalPolicy {
    /*synthetic*/ final JEditorPane this$0;
    
    JEditorPane$1(/*synthetic*/ final JEditorPane this$0) {
        this.this$0 = this$0;
        
    }
    
    public Component getComponentAfter(Container focusCycleRoot, Component aComponent) {
        if (focusCycleRoot != this$0 || (!this$0.isEditable() && this$0.getComponentCount() > 0)) {
            return super.getComponentAfter(focusCycleRoot, aComponent);
        } else {
            Container rootAncestor = this$0.getFocusCycleRootAncestor();
            return (rootAncestor != null) ? rootAncestor.getFocusTraversalPolicy().getComponentAfter(rootAncestor, this$0) : null;
        }
    }
    
    public Component getComponentBefore(Container focusCycleRoot, Component aComponent) {
        if (focusCycleRoot != this$0 || (!this$0.isEditable() && this$0.getComponentCount() > 0)) {
            return super.getComponentBefore(focusCycleRoot, aComponent);
        } else {
            Container rootAncestor = this$0.getFocusCycleRootAncestor();
            return (rootAncestor != null) ? rootAncestor.getFocusTraversalPolicy().getComponentBefore(rootAncestor, this$0) : null;
        }
    }
    
    public Component getDefaultComponent(Container focusCycleRoot) {
        return (focusCycleRoot != this$0 || (!this$0.isEditable() && this$0.getComponentCount() > 0)) ? super.getDefaultComponent(focusCycleRoot) : null;
    }
    
    protected boolean accept(Component aComponent) {
        return (aComponent != this$0) ? super.accept(aComponent) : false;
    }
}
