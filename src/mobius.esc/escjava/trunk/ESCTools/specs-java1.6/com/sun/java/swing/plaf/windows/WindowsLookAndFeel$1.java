package com.sun.java.swing.plaf.windows;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.util.*;
import sun.swing.BorderProvider;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class WindowsLookAndFeel$1 implements BorderProvider {
    /*synthetic*/ final WindowsLookAndFeel this$0;
    
    WindowsLookAndFeel$1(/*synthetic*/ final WindowsLookAndFeel this$0) {
        this.this$0 = this$0;
        
    }
    
    public Border getRolloverBorder(AbstractButton b) {
        return WindowsToolBarUI.getRolloverBorder(b);
    }
}
