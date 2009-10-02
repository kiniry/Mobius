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

class SwingUtilities2$2 implements UIDefaults$LazyValue {
    /*synthetic*/ final Class val$rootClass;
    /*synthetic*/ final String val$imageFile;
    /*synthetic*/ final Class val$baseClass;
    
    SwingUtilities2$2(/*synthetic*/ final Class val$baseClass, /*synthetic*/ final String val$imageFile, /*synthetic*/ final Class val$rootClass) {
        this.val$baseClass = val$baseClass;
        this.val$imageFile = val$imageFile;
        this.val$rootClass = val$rootClass;
        
    }
    
    public Object createValue(UIDefaults table) {
        byte[] buffer = (byte[])(byte[])java.security.AccessController.doPrivileged(new SwingUtilities2$2$1(this));
        if (buffer == null) {
            return null;
        }
        if (buffer.length == 0) {
            System.err.println("warning: " + val$imageFile + " is zero-length");
            return null;
        }
        return new IconUIResource(new ImageIcon(buffer));
    }
}
