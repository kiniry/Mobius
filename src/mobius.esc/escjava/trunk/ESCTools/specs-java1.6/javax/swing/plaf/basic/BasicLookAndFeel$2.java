package javax.swing.plaf.basic;

import java.awt.event.*;
import java.io.*;
import java.security.PrivilegedAction;
import java.util.*;
import java.lang.reflect.*;
import javax.sound.sampled.*;
import javax.swing.border.*;
import javax.swing.plaf.*;

class BasicLookAndFeel$2 implements PrivilegedAction {
    /*synthetic*/ final BasicLookAndFeel this$0;
    /*synthetic*/ final String val$soundFile;
    
    BasicLookAndFeel$2(/*synthetic*/ final BasicLookAndFeel this$0, /*synthetic*/ final String val$soundFile) {
        this.this$0 = this$0;
        this.val$soundFile = val$soundFile;
        
    }
    
    public Object run() {
        try {
            InputStream resource = this$0.getClass().getResourceAsStream(val$soundFile);
            if (resource == null) {
                return null;
            }
            BufferedInputStream in = new BufferedInputStream(resource);
            ByteArrayOutputStream out = new ByteArrayOutputStream(1024);
            byte[] buffer = new byte[1024];
            int n;
            while ((n = in.read(buffer)) > 0) {
                out.write(buffer, 0, n);
            }
            in.close();
            out.flush();
            buffer = out.toByteArray();
            return buffer;
        } catch (IOException ioe) {
            System.err.println(ioe.toString());
            return null;
        }
    }
}
