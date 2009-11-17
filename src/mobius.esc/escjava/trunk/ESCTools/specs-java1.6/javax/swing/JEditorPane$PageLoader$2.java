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

class JEditorPane$PageLoader$2 implements Runnable {
    /*synthetic*/ final JEditorPane$PageLoader this$1;
    
    JEditorPane$PageLoader$2(/*synthetic*/ final JEditorPane$PageLoader this$1) {
        this.this$1 = this$1;
        
    }
    
    public void run() {
        JEditorPane.access$000(this$1.this$0, "page", this$1.old, this$1.page);
    }
}
