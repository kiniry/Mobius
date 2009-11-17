package java.beans;

import java.applet.*;
import java.awt.*;
import java.beans.AppletInitializer;
import java.beans.beancontext.BeanContext;
import java.io.*;
import java.net.URL;

public class Beans {
    
    public Beans() {
        
    }
    
    public static Object instantiate(ClassLoader cls, String beanName) throws java.io.IOException, ClassNotFoundException {
        return Beans.instantiate(cls, beanName, null, null);
    }
    
    public static Object instantiate(ClassLoader cls, String beanName, BeanContext beanContext) throws java.io.IOException, ClassNotFoundException {
        return Beans.instantiate(cls, beanName, beanContext, null);
    }
    
    public static Object instantiate(ClassLoader cls, String beanName, BeanContext beanContext, AppletInitializer initializer) throws java.io.IOException, ClassNotFoundException {
        java.io.InputStream ins;
        java.io.ObjectInputStream oins = null;
        Object result = null;
        boolean serialized = false;
        java.io.IOException serex = null;
        if (cls == null) {
            try {
                cls = ClassLoader.getSystemClassLoader();
            } catch (SecurityException ex) {
            }
        }
        final String serName = beanName.replace('.', '/').concat(".ser");
        final ClassLoader loader = cls;
        ins = (InputStream)(InputStream)java.security.AccessController.doPrivileged(new Beans$1(loader, serName));
        if (ins != null) {
            try {
                if (cls == null) {
                    oins = new ObjectInputStream(ins);
                } else {
                    oins = new ObjectInputStreamWithLoader(ins, cls);
                }
                result = oins.readObject();
                serialized = true;
                oins.close();
            } catch (java.io.IOException ex) {
                ins.close();
                serex = ex;
            } catch (ClassNotFoundException ex) {
                ins.close();
                throw ex;
            }
        }
        if (result == null) {
            Class cl;
            try {
                if (cls == null) {
                    cl = Class.forName(beanName);
                } else {
                    cl = cls.loadClass(beanName);
                }
            } catch (ClassNotFoundException ex) {
                if (serex != null) {
                    throw serex;
                }
                throw ex;
            }
            try {
                result = cl.newInstance();
            } catch (Exception ex) {
                throw new ClassNotFoundException("" + cl + " : " + ex, ex);
            }
        }
        if (result != null) {
            AppletStub stub = null;
            if (result instanceof Applet) {
                Applet applet = (Applet)(Applet)result;
                boolean needDummies = initializer == null;
                if (needDummies) {
                    final String resourceName;
                    if (serialized) {
                        resourceName = beanName.replace('.', '/').concat(".ser");
                    } else {
                        resourceName = beanName.replace('.', '/').concat(".class");
                    }
                    URL objectUrl = null;
                    URL codeBase = null;
                    URL docBase = null;
                    final ClassLoader cloader = cls;
                    objectUrl = (URL)(URL)java.security.AccessController.doPrivileged(new Beans$2(cloader, resourceName));
                    if (objectUrl != null) {
                        String s = objectUrl.toExternalForm();
                        if (s.endsWith(resourceName)) {
                            int ix = s.length() - resourceName.length();
                            codeBase = new URL(s.substring(0, ix));
                            docBase = codeBase;
                            ix = s.lastIndexOf('/');
                            if (ix >= 0) {
                                docBase = new URL(s.substring(0, ix + 1));
                            }
                        }
                    }
                    BeansAppletContext context = new BeansAppletContext(applet);
                    stub = (AppletStub)new BeansAppletStub(applet, context, codeBase, docBase);
                    applet.setStub(stub);
                } else {
                    initializer.initialize(applet, beanContext);
                }
                if (beanContext != null) {
                    beanContext.add(result);
                }
                if (!serialized) {
                    applet.setSize(100, 100);
                    applet.init();
                }
                if (needDummies) {
                    ((BeansAppletStub)(BeansAppletStub)stub).active = true;
                } else initializer.activate(applet);
            } else if (beanContext != null) beanContext.add(result);
        }
        return result;
    }
    
    public static Object getInstanceOf(Object bean, Class targetType) {
        return bean;
    }
    
    public static boolean isInstanceOf(Object bean, Class targetType) {
        return Introspector.isSubclass(bean.getClass(), targetType);
    }
    
    public static boolean isDesignTime() {
        return designTime;
    }
    
    public static boolean isGuiAvailable() {
        return guiAvailable;
    }
    
    public static void setDesignTime(boolean isDesignTime) throws SecurityException {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPropertiesAccess();
        }
        designTime = isDesignTime;
    }
    
    public static void setGuiAvailable(boolean isGuiAvailable) throws SecurityException {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPropertiesAccess();
        }
        guiAvailable = isGuiAvailable;
    }
    private static boolean designTime;
    private static boolean guiAvailable;
    static {
        guiAvailable = !GraphicsEnvironment.isHeadless();
    }
}
