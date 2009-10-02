package javax.swing;

import java.applet.*;
import java.awt.*;
import java.awt.event.*;
import java.lang.reflect.*;
import javax.accessibility.*;

class SwingUtilities$SharedOwnerFrame extends Frame implements WindowListener {
    
    SwingUtilities$SharedOwnerFrame() {
        
    }
    
    public void addNotify() {
        super.addNotify();
        installListeners();
    }
    
    void installListeners() {
        Window[] windows = getOwnedWindows();
        for (int ind = 0; ind < windows.length; ind++) {
            Window window = windows[ind];
            if (window != null) {
                window.removeWindowListener(this);
                window.addWindowListener(this);
            }
        }
    }
    
    public void windowClosed(WindowEvent e) {
        synchronized (getTreeLock()) {
            Window[] windows = getOwnedWindows();
            for (int ind = 0; ind < windows.length; ind++) {
                Window window = windows[ind];
                if (window != null) {
                    if (window.isDisplayable()) {
                        return;
                    }
                    window.removeWindowListener(this);
                }
            }
            dispose();
        }
    }
    
    public void windowOpened(WindowEvent e) {
    }
    
    public void windowClosing(WindowEvent e) {
    }
    
    public void windowIconified(WindowEvent e) {
    }
    
    public void windowDeiconified(WindowEvent e) {
    }
    
    public void windowActivated(WindowEvent e) {
    }
    
    public void windowDeactivated(WindowEvent e) {
    }
    
    public void show() {
    }
    
    public void dispose() {
        try {
            getToolkit().getSystemEventQueue();
            super.dispose();
        } catch (Exception e) {
        }
    }
}
