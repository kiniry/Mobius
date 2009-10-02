package com.sun.java.swing.plaf.windows;

import java.awt.*;
import java.beans.*;
import java.lang.ref.*;
import javax.swing.*;
import javax.swing.plaf.*;

class DesktopProperty$WeakPCL extends WeakReference implements PropertyChangeListener {
    private Toolkit kit;
    private String key;
    private LookAndFeel laf;
    
    DesktopProperty$WeakPCL(Object target, Toolkit kit, String key, LookAndFeel laf) {
        super(target, DesktopProperty.access$200());
        this.kit = kit;
        this.key = key;
        this.laf = laf;
    }
    
    public void propertyChange(PropertyChangeEvent pce) {
        DesktopProperty property = (DesktopProperty)(DesktopProperty)get();
        if (property == null || laf != UIManager.getLookAndFeel()) {
            dispose();
        } else {
            property.invalidate();
            property.updateUI();
        }
    }
    
    void dispose() {
        kit.removePropertyChangeListener(key, this);
    }
}
