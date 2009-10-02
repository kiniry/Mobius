package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.applet.Applet;
import java.awt.Component;
import java.awt.Window;
import java.awt.event.*;
import java.awt.AWTEvent;
import java.util.*;

class BasicPopupMenuUI$MouseGrabber implements ChangeListener, AWTEventListener, ComponentListener, WindowListener {
    Window grabbedWindow;
    MenuElement[] lastPathSelected;
    
    public BasicPopupMenuUI$MouseGrabber() {
        
        MenuSelectionManager msm = MenuSelectionManager.defaultManager();
        msm.addChangeListener(this);
        this.lastPathSelected = msm.getSelectedPath();
        if (this.lastPathSelected.length != 0) {
            grabWindow(this.lastPathSelected);
        }
    }
    
    void grabWindow(MenuElement[] newPath) {
        java.security.AccessController.doPrivileged(new BasicPopupMenuUI$MouseGrabber$1(this));
        Component invoker = newPath[0].getComponent();
        if (invoker instanceof JPopupMenu) {
            invoker = ((JPopupMenu)(JPopupMenu)invoker).getInvoker();
        }
        grabbedWindow = invoker instanceof Window ? (Window)(Window)invoker : SwingUtilities.getWindowAncestor(invoker);
        if (grabbedWindow != null) {
            grabbedWindow.addComponentListener(this);
            grabbedWindow.addWindowListener(this);
        }
    }
    
    void ungrabWindow() {
        java.security.AccessController.doPrivileged(new BasicPopupMenuUI$MouseGrabber$2(this));
        if (grabbedWindow != null) {
            grabbedWindow.removeComponentListener(this);
            grabbedWindow.removeWindowListener(this);
            grabbedWindow = null;
        }
    }
    
    public void stateChanged(ChangeEvent e) {
        MenuSelectionManager msm = MenuSelectionManager.defaultManager();
        MenuElement[] p = msm.getSelectedPath();
        if (lastPathSelected.length == 0 && p.length != 0) {
            grabWindow(p);
        }
        if (lastPathSelected.length != 0 && p.length == 0) {
            ungrabWindow();
        }
        lastPathSelected = p;
    }
    
    public void eventDispatched(AWTEvent ev) {
        switch (ev.getID()) {
        case MouseEvent.MOUSE_PRESSED: 
            Component src = (Component)(Component)ev.getSource();
            if (isInPopup(src) || (src instanceof JMenu && ((JMenu)(JMenu)src).isSelected())) {
                return;
            }
            if (!(src instanceof JComponent) || !(((JComponent)(JComponent)src).getClientProperty("doNotCancelPopup") == BasicComboBoxUI.HIDE_POPUP_KEY)) {
                cancelPopupMenu();
                boolean consumeEvent = UIManager.getBoolean("PopupMenu.consumeEventOnClose");
                if (consumeEvent && !(src instanceof MenuElement)) {
                    ((MouseEvent)(MouseEvent)ev).consume();
                }
            }
            break;
        
        case MouseEvent.MOUSE_RELEASED: 
            src = (Component)(Component)ev.getSource();
            if (!(src instanceof MenuElement)) {
                break;
            }
            if (src instanceof JMenu || !(src instanceof JMenuItem)) {
                MenuSelectionManager.defaultManager().processMouseEvent((MouseEvent)(MouseEvent)ev);
            }
            break;
        
        case MouseEvent.MOUSE_DRAGGED: 
            src = (Component)(Component)ev.getSource();
            if (!(src instanceof MenuElement)) {
                break;
            }
            MenuSelectionManager.defaultManager().processMouseEvent((MouseEvent)(MouseEvent)ev);
            break;
        
        case MouseEvent.MOUSE_WHEEL: 
            if (isInPopup((Component)(Component)ev.getSource())) {
                return;
            }
            cancelPopupMenu();
            break;
        
        }
    }
    
    boolean isInPopup(Component src) {
        for (Component c = src; c != null; c = c.getParent()) {
            if (c instanceof Applet || c instanceof Window) {
                break;
            } else if (c instanceof JPopupMenu) {
                return true;
            }
        }
        return false;
    }
    
    void cancelPopupMenu() {
        JPopupMenu firstPopup = (JPopupMenu)(JPopupMenu)BasicPopupMenuUI.getFirstPopup();
        List popups = BasicPopupMenuUI.getPopups();
        Iterator iter = popups.iterator();
        while (iter.hasNext()) {
            JPopupMenu popup = (JPopupMenu)(JPopupMenu)iter.next();
            popup.putClientProperty("JPopupMenu.firePopupMenuCanceled", Boolean.TRUE);
        }
        MenuSelectionManager.defaultManager().clearSelectedPath();
    }
    
    public void componentResized(ComponentEvent e) {
        cancelPopupMenu();
    }
    
    public void componentMoved(ComponentEvent e) {
        cancelPopupMenu();
    }
    
    public void componentShown(ComponentEvent e) {
        cancelPopupMenu();
    }
    
    public void componentHidden(ComponentEvent e) {
        cancelPopupMenu();
    }
    
    public void windowClosing(WindowEvent e) {
        cancelPopupMenu();
    }
    
    public void windowClosed(WindowEvent e) {
        cancelPopupMenu();
    }
    
    public void windowIconified(WindowEvent e) {
        cancelPopupMenu();
    }
    
    public void windowDeactivated(WindowEvent e) {
        if (BasicPopupMenuUI.access$300()) {
            cancelPopupMenu();
        }
    }
    
    public void windowOpened(WindowEvent e) {
    }
    
    public void windowDeiconified(WindowEvent e) {
    }
    
    public void windowActivated(WindowEvent e) {
    }
}
