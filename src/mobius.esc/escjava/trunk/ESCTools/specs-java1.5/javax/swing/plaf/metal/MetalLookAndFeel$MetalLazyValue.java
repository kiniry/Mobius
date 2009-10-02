package javax.swing.plaf.metal;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.util.*;
import java.lang.reflect.*;
import java.security.AccessController;

class MetalLookAndFeel$MetalLazyValue implements UIDefaults$LazyValue {
    
    /*synthetic*/ static String access$000(MetalLookAndFeel$MetalLazyValue x0) {
        return x0.methodName;
    }
    private String className;
    private String methodName;
    
    MetalLookAndFeel$MetalLazyValue(String name) {
        
        this.className = name;
    }
    
    MetalLookAndFeel$MetalLazyValue(String name, String methodName) {
        this(name);
        this.methodName = methodName;
    }
    
    public Object createValue(UIDefaults table) {
        try {
            final Class c = Class.forName(className);
            if (methodName == null) {
                return c.newInstance();
            }
            Method method = (Method)(Method)AccessController.doPrivileged(new MetalLookAndFeel$MetalLazyValue$1(this, c));
            if (method != null) {
                return method.invoke(null, null);
            }
        } catch (ClassNotFoundException cnfe) {
        } catch (InstantiationException ie) {
        } catch (IllegalAccessException iae) {
        } catch (InvocationTargetException ite) {
        }
        return null;
    }
}
