package javax.swing;

import javax.swing.border.*;
import java.lang.reflect.*;
import java.lang.reflect.Method;
import java.security.PrivilegedAction;
import sun.reflect.misc.MethodUtil;

class UIDefaults$ProxyLazyValue$1 implements PrivilegedAction {
    /*synthetic*/ final UIDefaults$ProxyLazyValue this$0;
    /*synthetic*/ final UIDefaults val$table;
    
    UIDefaults$ProxyLazyValue$1(/*synthetic*/ final UIDefaults$ProxyLazyValue this$0, /*synthetic*/ final UIDefaults val$table) {
        this.this$0 = this$0;
        this.val$table = val$table;
        
    }
    
    public Object run() {
        try {
            Class c;
            Object cl;
            if (val$table == null || !((cl = val$table.get("ClassLoader")) instanceof ClassLoader)) {
                cl = Thread.currentThread().getContextClassLoader();
                if (cl == null) {
                    cl = ClassLoader.getSystemClassLoader();
                }
            }
            c = Class.forName(UIDefaults.ProxyLazyValue.access$000(this$0), true, (ClassLoader)(ClassLoader)cl);
            if (UIDefaults.ProxyLazyValue.access$100(this$0) != null) {
                Class[] types = UIDefaults.ProxyLazyValue.access$300(this$0, UIDefaults.ProxyLazyValue.access$200(this$0));
                Method m = c.getMethod(UIDefaults.ProxyLazyValue.access$100(this$0), types);
                return MethodUtil.invoke(m, c, UIDefaults.ProxyLazyValue.access$200(this$0));
            } else {
                Class[] types = UIDefaults.ProxyLazyValue.access$300(this$0, UIDefaults.ProxyLazyValue.access$200(this$0));
                Constructor constructor = c.getConstructor(types);
                return constructor.newInstance(UIDefaults.ProxyLazyValue.access$200(this$0));
            }
        } catch (Exception e) {
        }
        return null;
    }
}
