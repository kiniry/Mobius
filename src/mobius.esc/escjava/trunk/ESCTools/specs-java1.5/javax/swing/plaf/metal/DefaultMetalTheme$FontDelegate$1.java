package javax.swing.plaf.metal;

import javax.swing.plaf.*;
import javax.swing.*;
import java.awt.*;

class DefaultMetalTheme$FontDelegate$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final DefaultMetalTheme$FontDelegate this$0;
    /*synthetic*/ final int val$key;
    
    DefaultMetalTheme$FontDelegate$1(/*synthetic*/ final DefaultMetalTheme$FontDelegate this$0, /*synthetic*/ final int val$key) {
        this.this$0 = this$0;
        this.val$key = val$key;
        
    }
    
    public Object run() {
        return Font.getFont(DefaultMetalTheme.getDefaultPropertyName(val$key));
    }
}
