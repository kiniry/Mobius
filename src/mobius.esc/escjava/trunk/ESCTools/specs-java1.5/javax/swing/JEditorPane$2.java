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

class JEditorPane$2 implements Runnable {
    /*synthetic*/ final JEditorPane this$0;
    /*synthetic*/ final String val$reference;
    
    JEditorPane$2(/*synthetic*/ final JEditorPane this$0, /*synthetic*/ final String val$reference) {
        this.this$0 = this$0;
        this.val$reference = val$reference;
        
    }
    
    public void run() {
        this$0.scrollToReference(val$reference);
    }
}
