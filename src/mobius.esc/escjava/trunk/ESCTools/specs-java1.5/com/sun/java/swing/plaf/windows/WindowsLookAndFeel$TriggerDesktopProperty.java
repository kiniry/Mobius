package com.sun.java.swing.plaf.windows;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.util.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class WindowsLookAndFeel$TriggerDesktopProperty extends DesktopProperty {
    /*synthetic*/ final WindowsLookAndFeel this$0;
    
    WindowsLookAndFeel$TriggerDesktopProperty(/*synthetic*/ final WindowsLookAndFeel this$0, String key) {
        this.this$0 = this$0;
        super(key, null, WindowsLookAndFeel.access$000(this$0));
        getValueFromDesktop();
    }
    
    protected void updateUI() {
        super.updateUI();
        getValueFromDesktop();
    }
}
