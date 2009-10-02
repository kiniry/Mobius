package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.io.*;
import java.util.*;
import javax.swing.event.*;
import javax.swing.tree.*;
import javax.accessibility.*;

public class JTree$TreeSelectionRedirector implements Serializable, TreeSelectionListener {
    /*synthetic*/ final JTree this$0;
    
    protected JTree$TreeSelectionRedirector(/*synthetic*/ final JTree this$0) {
        this.this$0 = this$0;
        
    }
    
    public void valueChanged(TreeSelectionEvent e) {
        TreeSelectionEvent newE;
        newE = (TreeSelectionEvent)(TreeSelectionEvent)e.cloneWithSource(this$0);
        this$0.fireValueChanged(newE);
    }
}
