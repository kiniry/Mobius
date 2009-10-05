package com.sun.java.swing.plaf.windows;

import javax.swing.plaf.basic.*;
import javax.swing.*;
import javax.swing.plaf.ActionMapUIResource;
import javax.swing.plaf.ComponentUI;
import java.awt.event.HierarchyListener;
import java.awt.event.WindowListener;
import java.awt.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;
import com.sun.java.swing.plaf.windows.XPStyle.*;

public class WindowsMenuBarUI extends BasicMenuBarUI {
    
    /*synthetic*/ static void access$400(WindowsMenuBarUI x0) {
        x0.uninstallWindowListener();
    }
    
    /*synthetic*/ static void access$300(WindowsMenuBarUI x0) {
        x0.installWindowListener();
    }
    
    /*synthetic*/ static JMenuBar access$200(WindowsMenuBarUI x0) {
        return x0.menuBar;
    }
    
    /*synthetic*/ static JMenuBar access$100(WindowsMenuBarUI x0) {
        return x0.menuBar;
    }
    
    /*synthetic*/ static JMenuBar access$000(WindowsMenuBarUI x0) {
        return x0.menuBar;
    }
    
    public WindowsMenuBarUI() {
        
    }
    private WindowListener windowListener = null;
    private HierarchyListener hierarchyListener = null;
    private Window window = null;
    
    public static ComponentUI createUI(JComponent x) {
        return new WindowsMenuBarUI();
    }
    
    protected void uninstallListeners() {
        uninstallWindowListener();
        if (hierarchyListener != null) {
            menuBar.removeHierarchyListener(hierarchyListener);
            hierarchyListener = null;
        }
        super.uninstallListeners();
    }
    
    private void installWindowListener() {
        if (windowListener == null) {
            Component component = menuBar.getTopLevelAncestor();
            if (component instanceof Window) {
                window = (Window)(Window)component;
                windowListener = new WindowsMenuBarUI$1(this);
                ((Window)(Window)component).addWindowListener(windowListener);
            }
        }
    }
    
    private void uninstallWindowListener() {
        if (windowListener != null && window != null) {
            window.removeWindowListener(windowListener);
        }
        window = null;
        windowListener = null;
    }
    
    protected void installListeners() {
        if (WindowsLookAndFeel.isOnVista()) {
            installWindowListener();
            hierarchyListener = new WindowsMenuBarUI$2(this);
            menuBar.addHierarchyListener(hierarchyListener);
        }
        super.installListeners();
    }
    
    protected void installKeyboardActions() {
        super.installKeyboardActions();
        ActionMap map = SwingUtilities.getUIActionMap(menuBar);
        if (map == null) {
            map = new ActionMapUIResource();
            SwingUtilities.replaceUIActionMap(menuBar, map);
        }
        map.put("takeFocus", new WindowsMenuBarUI$TakeFocus(null));
    }
    {
    }
    
    public void paint(Graphics g, JComponent c) {
        if (WindowsMenuItemUI.isVistaPainting()) {
            XPStyle xp = XPStyle.getXP();
            XPStyle$Skin skin;
            skin = xp.getSkin(c, TMSchema$Part.MP_BARBACKGROUND);
            int width = c.getWidth();
            int height = c.getHeight();
            TMSchema$State state = isActive(c) ? TMSchema$State.ACTIVE : TMSchema$State.INACTIVE;
            skin.paintSkin(g, 0, 0, width, height, state);
        } else {
            super.paint(g, c);
        }
    }
    
    static boolean isActive(JComponent c) {
        JRootPane rootPane = c.getRootPane();
        if (rootPane != null) {
            Component component = rootPane.getParent();
            if (component instanceof Window) {
                return ((Window)(Window)component).isActive();
            }
        }
        return true;
    }
}
