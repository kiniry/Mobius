package com.sun.java.swing.plaf.windows;

import java.awt.*;
import java.beans.*;
import java.lang.ref.*;
import javax.swing.*;
import javax.swing.plaf.*;

public class DesktopProperty implements UIDefaults$ActiveValue {
    
    /*synthetic*/ static ReferenceQueue access$200() {
        return queue;
    }
    
    /*synthetic*/ static void access$100(boolean x0) {
        setUpdatePending(x0);
    }
    
    /*synthetic*/ static void access$000() {
        updateAllUIs();
    }
    private static boolean updatePending;
    private static ReferenceQueue queue;
    private DesktopProperty$WeakPCL pcl;
    private String key;
    private Object value;
    private Object fallback;
    private Toolkit toolkit;
    static {
        queue = new ReferenceQueue();
    }
    
    static void flushUnreferencedProperties() {
        DesktopProperty$WeakPCL pcl;
        while ((pcl = (DesktopProperty$WeakPCL)(DesktopProperty$WeakPCL)queue.poll()) != null) {
            pcl.dispose();
        }
    }
    
    private static synchronized void setUpdatePending(boolean update) {
        updatePending = update;
    }
    
    private static synchronized boolean isUpdatePending() {
        return updatePending;
    }
    
    private static void updateAllUIs() {
        Class uiClass = UIManager.getLookAndFeel().getClass();
        if (uiClass.getPackage().equals(DesktopProperty.class.getPackage())) {
            XPStyle.invalidateStyle();
        }
        Frame[] appFrames = Frame.getFrames();
        for (int j = 0; j < appFrames.length; j++) {
            updateWindowUI(appFrames[j]);
        }
    }
    
    private static void updateWindowUI(Window window) {
        SwingUtilities.updateComponentTreeUI(window);
        Window[] ownedWins = window.getOwnedWindows();
        for (int i = 0; i < ownedWins.length; i++) {
            updateWindowUI(ownedWins[i]);
        }
    }
    
    public DesktopProperty(String key, Object fallback, Toolkit toolkit) {
        
        this.key = key;
        this.fallback = fallback;
        this.toolkit = toolkit;
        flushUnreferencedProperties();
    }
    
    public Object createValue(UIDefaults table) {
        if (value == null) {
            value = configureValue(getValueFromDesktop());
            if (value == null) {
                value = configureValue(getDefaultValue());
            }
        }
        return value;
    }
    
    protected Object getValueFromDesktop() {
        if (this.toolkit == null) {
            this.toolkit = Toolkit.getDefaultToolkit();
        }
        Object value = toolkit.getDesktopProperty(getKey());
        pcl = new DesktopProperty$WeakPCL(this, toolkit, getKey(), UIManager.getLookAndFeel());
        toolkit.addPropertyChangeListener(getKey(), pcl);
        return value;
    }
    
    protected Object getDefaultValue() {
        return fallback;
    }
    
    public void invalidate() {
        if (pcl != null) {
            toolkit.removePropertyChangeListener(getKey(), pcl);
            toolkit = null;
            pcl = null;
            value = null;
        }
    }
    
    protected void updateUI() {
        if (!isUpdatePending()) {
            setUpdatePending(true);
            Runnable uiUpdater = new DesktopProperty$1(this);
            SwingUtilities.invokeLater(uiUpdater);
        }
    }
    
    protected Object configureValue(Object value) {
        if (value != null) {
            if (value instanceof Color) {
                return new ColorUIResource((Color)(Color)value);
            } else if (value instanceof Font) {
                return new FontUIResource((Font)(Font)value);
            } else if (value instanceof UIDefaults$LazyValue) {
                value = ((UIDefaults$LazyValue)(UIDefaults$LazyValue)value).createValue(null);
            } else if (value instanceof UIDefaults$ActiveValue) {
                value = ((UIDefaults$ActiveValue)(UIDefaults$ActiveValue)value).createValue(null);
            }
        }
        return value;
    }
    
    protected String getKey() {
        return key;
    }
    {
    }
}
