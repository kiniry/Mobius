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

class JEditorPane$PageStream extends FilterInputStream {
    boolean canceled;
    
    public JEditorPane$PageStream(InputStream i) {
        super(i);
        canceled = false;
    }
    
    public synchronized void cancel() {
        canceled = true;
    }
    
    protected synchronized void checkCanceled() throws IOException {
        if (canceled) {
            throw new IOException("page canceled");
        }
    }
    
    public int read() throws IOException {
        checkCanceled();
        return super.read();
    }
    
    public long skip(long n) throws IOException {
        checkCanceled();
        return super.skip(n);
    }
    
    public int available() throws IOException {
        checkCanceled();
        return super.available();
    }
    
    public void reset() throws IOException {
        checkCanceled();
        super.reset();
    }
}
