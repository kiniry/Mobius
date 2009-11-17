package com.sun.java.swing;

import java.security.*;
import java.lang.reflect.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.font.*;
import java.awt.geom.*;
import javax.swing.*;
import javax.swing.plaf.*;
import java.io.*;

class SwingUtilities2$2$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final SwingUtilities2$2 this$0;
    
    SwingUtilities2$2$1(/*synthetic*/ final SwingUtilities2$2 this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        try {
            InputStream resource = null;
            Class srchClass = this$0.val$baseClass;
            while (srchClass != null) {
                resource = srchClass.getResourceAsStream(this$0.val$imageFile);
                if (resource != null || srchClass == this$0.val$rootClass) {
                    break;
                }
                srchClass = srchClass.getSuperclass();
            }
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
            return out.toByteArray();
        } catch (IOException ioe) {
            System.err.println(ioe.toString());
        }
        return null;
    }
}
