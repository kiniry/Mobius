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

class JEditorPane$PageLoader extends Thread {
    /*synthetic*/ final JEditorPane this$0;
    
    JEditorPane$PageLoader(/*synthetic*/ final JEditorPane this$0, Document doc, InputStream in, int priority, URL old, URL page) {
        this.this$0 = this$0;
        
        setPriority(priority);
        this.in = in;
        this.old = old;
        this.page = page;
        this.doc = doc;
    }
    
    public void run() {
        try {
            this$0.read(in, doc);
            synchronized (this$0) {
                this$0.loading = null;
            }
            URL page = (URL)(URL)doc.getProperty(Document.StreamDescriptionProperty);
            String reference = page.getRef();
            if (reference != null) {
                Runnable callScrollToReference = new JEditorPane$PageLoader$1(this);
                SwingUtilities.invokeLater(callScrollToReference);
            }
        } catch (IOException ioe) {
            UIManager.getLookAndFeel().provideErrorFeedback(this$0);
        } finally {
            SwingUtilities.invokeLater(new JEditorPane$PageLoader$2(this));
        }
    }
    InputStream in;
    URL old;
    URL page;
    Document doc;
}
