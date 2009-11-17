package com.sun.java.swing.plaf.windows;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.awt.event.ActionEvent;
import java.util.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class WindowsLookAndFeel$AudioAction extends AbstractAction {
    private Runnable audioRunnable;
    private String audioResource;
    
    public WindowsLookAndFeel$AudioAction(String name, String resource) {
        super(name);
        audioResource = resource;
    }
    
    public void actionPerformed(ActionEvent e) {
        if (audioRunnable == null) {
            audioRunnable = (Runnable)(Runnable)Toolkit.getDefaultToolkit().getDesktopProperty(audioResource);
        }
        if (audioRunnable != null) {
            new Thread(audioRunnable).start();
        }
    }
}
