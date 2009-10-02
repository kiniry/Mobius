package java.awt;

import java.awt.event.*;
import java.awt.peer.*;
import java.awt.*;
import sun.awt.HeadlessToolkit;

class Toolkit$2 implements java.security.PrivilegedAction {
    
    Toolkit$2() {
        
    }
    
    public Object run() {
        String nm = null;
        Class cls = null;
        try {
            String defaultToolkit;
            if (System.getProperty("os.name").equals("Linux")) {
                defaultToolkit = "sun.awt.X11.XToolkit";
            } else {
                defaultToolkit = "sun.awt.motif.MToolkit";
            }
            nm = System.getProperty("awt.toolkit", defaultToolkit);
            try {
                cls = Class.forName(nm);
            } catch (ClassNotFoundException e) {
                ClassLoader cl = ClassLoader.getSystemClassLoader();
                if (cl != null) {
                    try {
                        cls = cl.loadClass(nm);
                    } catch (ClassNotFoundException ee) {
                        throw new AWTError("Toolkit not found: " + nm);
                    }
                }
            }
            if (cls != null) {
                Toolkit.access$002((Toolkit)(Toolkit)cls.newInstance());
                if (GraphicsEnvironment.isHeadless()) {
                    Toolkit.access$002(new HeadlessToolkit(Toolkit.access$000()));
                }
            }
        } catch (InstantiationException e) {
            throw new AWTError("Could not instantiate Toolkit: " + nm);
        } catch (IllegalAccessException e) {
            throw new AWTError("Could not access Toolkit: " + nm);
        }
        return null;
    }
}
