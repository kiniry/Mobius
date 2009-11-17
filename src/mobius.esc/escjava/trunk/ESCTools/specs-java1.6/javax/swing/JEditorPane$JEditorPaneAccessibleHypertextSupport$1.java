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

class JEditorPane$JEditorPaneAccessibleHypertextSupport$1 implements DocumentListener {
    /*synthetic*/ final JEditorPane$JEditorPaneAccessibleHypertextSupport this$1;
    /*synthetic*/ final JEditorPane val$this$0;
    
    JEditorPane$JEditorPaneAccessibleHypertextSupport$1(/*synthetic*/ final JEditorPane$JEditorPaneAccessibleHypertextSupport this$1, /*synthetic*/ final JEditorPane val$this$0) {
        this.this$1 = this$1;
        this.val$this$0 = val$this$0;
        
    }
    
    public void changedUpdate(DocumentEvent theEvent) {
        this$1.linksValid = false;
    }
    
    public void insertUpdate(DocumentEvent theEvent) {
        this$1.linksValid = false;
    }
    
    public void removeUpdate(DocumentEvent theEvent) {
        this$1.linksValid = false;
    }
}
