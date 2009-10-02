package javax.swing.plaf.metal;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.util.*;
import java.lang.reflect.*;
import java.security.PrivilegedAction;

class MetalLookAndFeel$MetalLazyValue$1 implements PrivilegedAction {
    /*synthetic*/ final MetalLookAndFeel$MetalLazyValue this$0;
    /*synthetic*/ final Class val$c;
    
    MetalLookAndFeel$MetalLazyValue$1(/*synthetic*/ final MetalLookAndFeel$MetalLazyValue this$0, /*synthetic*/ final Class val$c) {
        this.this$0 = this$0;
        this.val$c = val$c;
        
    }
    
    public Object run() {
        Method[] methods = val$c.getDeclaredMethods();
        for (int counter = methods.length - 1; counter >= 0; counter--) {
            if (methods[counter].getName().equals(MetalLookAndFeel.MetalLazyValue.access$000(this$0))) {
                methods[counter].setAccessible(true);
                return methods[counter];
            }
        }
        return null;
    }
}
