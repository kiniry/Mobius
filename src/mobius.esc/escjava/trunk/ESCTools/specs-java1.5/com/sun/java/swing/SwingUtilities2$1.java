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

class SwingUtilities2$1 implements java.security.PrivilegedAction {
    
    SwingUtilities2$1() {
        
    }
    
    public Object run() {
        Field field = null;
        try {
            field = InputEvent.class.getDeclaredField("canAccessSystemClipboard");
            field.setAccessible(true);
            return field;
        } catch (SecurityException e) {
        } catch (NoSuchFieldException e) {
        }
        return null;
    }
}
