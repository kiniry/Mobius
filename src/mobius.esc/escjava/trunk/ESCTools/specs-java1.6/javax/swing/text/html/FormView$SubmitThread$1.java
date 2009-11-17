package javax.swing.text.html;

import java.net.*;
import java.io.*;
import java.awt.*;
import java.awt.event.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;

class FormView$SubmitThread$1 implements Runnable {
    /*synthetic*/ final FormView$SubmitThread this$1;
    
    FormView$SubmitThread$1(/*synthetic*/ final FormView$SubmitThread this$1) {
        this.this$1 = this$1;
        
    }
    
    public void run() {
        JEditorPane c = (JEditorPane)(JEditorPane)this$1.this$0.getContainer();
        if (this$1.hdoc.isFrameDocument()) {
            c.fireHyperlinkUpdate(FormView.SubmitThread.access$100(this$1));
        } else {
            try {
                c.setPage(this$1.url);
            } catch (IOException e) {
            }
        }
    }
}
