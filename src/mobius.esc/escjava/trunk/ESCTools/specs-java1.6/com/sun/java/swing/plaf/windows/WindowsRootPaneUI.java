package com.sun.java.swing.plaf.windows;

import javax.swing.JComponent;
import javax.swing.plaf.ComponentUI;
import javax.swing.plaf.basic.BasicRootPaneUI;

public class WindowsRootPaneUI extends BasicRootPaneUI {
    
    public WindowsRootPaneUI() {
        
    }
    private static final WindowsRootPaneUI windowsRootPaneUI = new WindowsRootPaneUI();
    static final WindowsRootPaneUI$AltProcessor altProcessor = new WindowsRootPaneUI$AltProcessor();
    
    public static ComponentUI createUI(JComponent c) {
        return windowsRootPaneUI;
    }
    {
    }
}
