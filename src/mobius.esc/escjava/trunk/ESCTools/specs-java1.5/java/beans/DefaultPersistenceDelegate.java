package java.beans;

import java.util.*;
import java.lang.reflect.*;
import java.beans.*;
import java.io.*;
import sun.reflect.misc.*;

public class DefaultPersistenceDelegate extends PersistenceDelegate {
    private String[] constructor;
    private Boolean definesEquals;
    
    public DefaultPersistenceDelegate() {
        this(new String[0]);
    }
    
    public DefaultPersistenceDelegate(String[] constructorPropertyNames) {
        
        this.constructor = constructorPropertyNames;
    }
    
    private static boolean definesEquals(Class type) {
        try {
            type.getDeclaredMethod("equals", new Class[]{Object.class});
            return true;
        } catch (NoSuchMethodException e) {
            return false;
        }
    }
    
    private boolean definesEquals(Object instance) {
        if (definesEquals != null) {
            return (definesEquals == Boolean.TRUE);
        } else {
            boolean result = definesEquals(instance.getClass());
            definesEquals = result ? Boolean.TRUE : Boolean.FALSE;
            return result;
        }
    }
    
    protected boolean mutatesTo(Object oldInstance, Object newInstance) {
        return (constructor.length == 0) || !definesEquals(oldInstance) ? super.mutatesTo(oldInstance, newInstance) : oldInstance.equals(newInstance);
    }
    
    protected Expression instantiate(Object oldInstance, Encoder out) {
        int nArgs = constructor.length;
        Class type = oldInstance.getClass();
        Object[] constructorArgs = new Object[nArgs];
        for (int i = 0; i < nArgs; i++) {
            String name = constructor[i];
            Field f = null;
            try {
                f = type.getDeclaredField(name);
                f.setAccessible(true);
            } catch (NoSuchFieldException e) {
            }
            try {
                constructorArgs[i] = (f != null && !Modifier.isStatic(f.getModifiers())) ? f.get(oldInstance) : MethodUtil.invoke(ReflectionUtils.getPublicMethod(type, "get" + NameGenerator.capitalize(name), new Class[0]), oldInstance, new Object[0]);
            } catch (Exception e) {
                out.getExceptionListener().exceptionThrown(e);
            }
        }
        return new Expression(oldInstance, oldInstance.getClass(), "new", constructorArgs);
    }
    
    private boolean isTransient(Class type, PropertyDescriptor pd) {
        if (type == null) {
            return false;
        }
        String pName = pd.getName();
        BeanInfo info = MetaData.getBeanInfo(type);
        PropertyDescriptor[] propertyDescriptors = info.getPropertyDescriptors();
        for (int i = 0; i < propertyDescriptors.length; ++i) {
            PropertyDescriptor pd2 = propertyDescriptors[i];
            if (pName.equals(pd2.getName())) {
                Object value = pd2.getValue("transient");
                if (value != null) {
                    return Boolean.TRUE.equals(value);
                }
            }
        }
        return isTransient(type.getSuperclass(), pd);
    }
    
    private static boolean equals(Object o1, Object o2) {
        return (o1 == null) ? (o2 == null) : o1.equals(o2);
    }
    
    private void doProperty(Class type, PropertyDescriptor pd, Object oldInstance, Object newInstance, Encoder out) throws Exception {
        Method getter = pd.getReadMethod();
        Method setter = pd.getWriteMethod();
        if (getter != null && setter != null && !isTransient(type, pd)) {
            Expression oldGetExp = new Expression(oldInstance, getter.getName(), new Object[]{});
            Expression newGetExp = new Expression(newInstance, getter.getName(), new Object[]{});
            Object oldValue = oldGetExp.getValue();
            Object newValue = newGetExp.getValue();
            out.writeExpression(oldGetExp);
            if (!equals(newValue, out.get(oldValue))) {
                Object e = (Object[])(Object[])pd.getValue("enumerationValues");
                if (e instanceof Object[] && Array.getLength(e) % 3 == 0) {
                    Object[] a = (Object[])(Object[])e;
                    for (int i = 0; i < a.length; i = i + 3) {
                        try {
                            Field f = type.getField((String)(String)a[i]);
                            if (f.get(null).equals(oldValue)) {
                                out.remove(oldValue);
                                out.writeExpression(new Expression(oldValue, f, "get", new Object[]{null}));
                            }
                        } catch (Exception ex) {
                        }
                    }
                }
                invokeStatement(oldInstance, setter.getName(), new Object[]{oldValue}, out);
            }
        }
    }
    
    static void invokeStatement(Object instance, String methodName, Object[] args, Encoder out) {
        out.writeStatement(new Statement(instance, methodName, args));
    }
    
    private void initBean(Class type, Object oldInstance, Object newInstance, Encoder out) {
        BeanInfo info = MetaData.getBeanInfo(type);
        PropertyDescriptor[] propertyDescriptors = info.getPropertyDescriptors();
        for (int i = 0; i < propertyDescriptors.length; ++i) {
            try {
                doProperty(type, propertyDescriptors[i], oldInstance, newInstance, out);
            } catch (Exception e) {
                out.getExceptionListener().exceptionThrown(e);
            }
        }
        if (!java.awt.Component.class.isAssignableFrom(type)) {
            return;
        }
        EventSetDescriptor[] eventSetDescriptors = info.getEventSetDescriptors();
        for (int e = 0; e < eventSetDescriptors.length; e++) {
            EventSetDescriptor d = eventSetDescriptors[e];
            Class listenerType = d.getListenerType();
            if (listenerType == java.awt.event.ComponentListener.class) {
                continue;
            }
            if (listenerType == javax.swing.event.ChangeListener.class && type == javax.swing.JMenuItem.class) {
                continue;
            }
            EventListener[] oldL = new EventListener[0];
            EventListener[] newL = new EventListener[0];
            try {
                Method m = d.getGetListenerMethod();
                oldL = (EventListener[])(EventListener[])MethodUtil.invoke(m, oldInstance, new Object[]{});
                newL = (EventListener[])(EventListener[])MethodUtil.invoke(m, newInstance, new Object[]{});
            } catch (Throwable e2) {
                try {
                    Method m = type.getMethod("getListeners", new Class[]{Class.class});
                    oldL = (EventListener[])(EventListener[])MethodUtil.invoke(m, oldInstance, new Object[]{listenerType});
                    newL = (EventListener[])(EventListener[])MethodUtil.invoke(m, newInstance, new Object[]{listenerType});
                } catch (Exception e3) {
                    return;
                }
            }
            String addListenerMethodName = d.getAddListenerMethod().getName();
            for (int i = newL.length; i < oldL.length; i++) {
                invokeStatement(oldInstance, addListenerMethodName, new Object[]{oldL[i]}, out);
            }
            String removeListenerMethodName = d.getRemoveListenerMethod().getName();
            for (int i = oldL.length; i < newL.length; i++) {
                invokeStatement(oldInstance, removeListenerMethodName, new Object[]{oldL[i]}, out);
            }
        }
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        super.initialize(type, oldInstance, newInstance, out);
        if (oldInstance.getClass() == type) {
            initBean(type, oldInstance, newInstance, out);
        }
    }
}
