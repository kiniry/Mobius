package com.sun.java.swing.plaf.windows;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.util.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;
import com.sun.java.swing.plaf.windows.WindowsIconFactory.VistaMenuItemCheckIconFactory;

class WindowsLookAndFeel$2 implements UIDefaults$ActiveValue {
    /*synthetic*/ final WindowsLookAndFeel this$0;
    
    WindowsLookAndFeel$2(/*synthetic*/ final WindowsLookAndFeel this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object createValue(UIDefaults table) {
        return Integer.valueOf(WindowsIconFactory$VistaMenuItemCheckIconFactory.getIconWidth() + WindowsPopupMenuUI.getSpanBeforeGutter() + WindowsPopupMenuUI.getGutterWidth() + WindowsPopupMenuUI.getSpanAfterGutter());
    }
}
