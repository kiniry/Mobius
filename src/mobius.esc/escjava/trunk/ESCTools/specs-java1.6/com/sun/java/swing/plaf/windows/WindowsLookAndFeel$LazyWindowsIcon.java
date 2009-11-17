package com.sun.java.swing.plaf.windows;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.util.*;
import sun.awt.shell.ShellFolder;
import com.sun.java.swing.SwingUtilities2;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class WindowsLookAndFeel$LazyWindowsIcon implements UIDefaults$LazyValue {
    private String nativeImage;
    private String resource;
    
    WindowsLookAndFeel$LazyWindowsIcon(String nativeImage, String resource) {
        
        this.nativeImage = nativeImage;
        this.resource = resource;
    }
    
    public Object createValue(UIDefaults table) {
        if (nativeImage != null) {
            Image image = (Image)(Image)ShellFolder.get(nativeImage);
            if (image != null) {
                return new ImageIcon(image);
            }
        }
        return SwingUtilities2.makeIcon(getClass(), WindowsLookAndFeel.class, resource);
    }
}
