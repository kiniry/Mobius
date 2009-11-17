package javax.swing;

import javax.swing.border.*;
import java.lang.reflect.*;
import java.awt.Color;
import java.security.AccessController;
import java.security.AccessControlContext;

public class UIDefaults$ProxyLazyValue implements UIDefaults$LazyValue {
    
    /*synthetic*/ static Class[] access$300(UIDefaults$ProxyLazyValue x0, Object[] x1) {
        return x0.getClassArray(x1);
    }
    
    /*synthetic*/ static Object[] access$200(UIDefaults$ProxyLazyValue x0) {
        return x0.args;
    }
    
    /*synthetic*/ static String access$100(UIDefaults$ProxyLazyValue x0) {
        return x0.methodName;
    }
    
    /*synthetic*/ static String access$000(UIDefaults$ProxyLazyValue x0) {
        return x0.className;
    }
    private AccessControlContext acc;
    private String className;
    private String methodName;
    private Object[] args;
    
    public UIDefaults$ProxyLazyValue(String c) {
        this(c, (String)null);
    }
    
    public UIDefaults$ProxyLazyValue(String c, String m) {
        this(c, m, null);
    }
    
    public UIDefaults$ProxyLazyValue(String c, Object[] o) {
        this(c, null, o);
    }
    
    public UIDefaults$ProxyLazyValue(String c, String m, Object[] o) {
        
        acc = AccessController.getContext();
        className = c;
        methodName = m;
        if (o != null) {
            args = (Object[])(Object[])o.clone();
        }
    }
    
    public Object createValue(final UIDefaults table) {
        return AccessController.doPrivileged(new UIDefaults$ProxyLazyValue$1(this, table), acc);
    }
    
    private Class[] getClassArray(Object[] args) {
        Class[] types = null;
        if (args != null) {
            types = new Class[args.length];
            for (int i = 0; i < args.length; i++) {
                if (args[i] instanceof java.lang.Integer) {
                    types[i] = Integer.TYPE;
                } else if (args[i] instanceof java.lang.Boolean) {
                    types[i] = Boolean.TYPE;
                } else if (args[i] instanceof javax.swing.plaf.ColorUIResource) {
                    types[i] = Color.class;
                } else {
                    types[i] = args[i].getClass();
                }
            }
        }
        return types;
    }
    
    private String printArgs(Object[] array) {
        String s = "{";
        if (array != null) {
            for (int i = 0; i < array.length - 1; i++) {
                s = s.concat(array[i] + ",");
            }
            s = s.concat(array[array.length - 1] + "}");
        } else {
            s = s.concat("}");
        }
        return s;
    }
}
