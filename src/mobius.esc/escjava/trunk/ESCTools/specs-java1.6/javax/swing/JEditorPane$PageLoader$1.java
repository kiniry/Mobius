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

class JEditorPane$PageLoader$1 implements Runnable {
    /*synthetic*/ final JEditorPane$PageLoader this$1;
    
    JEditorPane$PageLoader$1(/*synthetic*/ final JEditorPane$PageLoader this$1) {
        this.this$1 = this$1;
        
    }
    
    public void run() {
        URL u = (URL)(URL)this$1.this$0.getDocument().getProperty(Document.StreamDescriptionProperty);
        String ref = u.getRef();
        this$1.this$0.scrollToReference(ref);
    }
}
