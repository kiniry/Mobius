package javax.swing.text.html;

import java.awt.*;
import javax.swing.*;
import javax.swing.text.*;
import java.beans.*;
import java.lang.reflect.*;

public class ObjectView extends ComponentView {
    
    public ObjectView(Element elem) {
        super(elem);
    }
    
    protected Component createComponent() {
        AttributeSet attr = getElement().getAttributes();
        String classname = (String)(String)attr.getAttribute(HTML$Attribute.CLASSID);
        try {
            Class c = Class.forName(classname, true, Thread.currentThread().getContextClassLoader());
            Object o = c.newInstance();
            if (o instanceof Component) {
                Component comp = (Component)(Component)o;
                setParameters(comp, attr);
                return comp;
            }
        } catch (Throwable e) {
        }
        return getUnloadableRepresentation();
    }
    
    Component getUnloadableRepresentation() {
        Component comp = new JLabel("??");
        comp.setForeground(Color.red);
        return comp;
    }
    
    private Class getClass(String classname) throws ClassNotFoundException {
        Class klass;
        Class docClass = getDocument().getClass();
        ClassLoader loader = docClass.getClassLoader();
        if (loader != null) {
            klass = loader.loadClass(classname);
        } else {
            klass = Class.forName(classname);
        }
        return klass;
    }
    
    private void setParameters(Component comp, AttributeSet attr) {
        Class k = comp.getClass();
        BeanInfo bi;
        try {
            bi = Introspector.getBeanInfo(k);
        } catch (IntrospectionException ex) {
            System.err.println("introspector failed, ex: " + ex);
            return;
        }
        PropertyDescriptor[] props = bi.getPropertyDescriptors();
        for (int i = 0; i < props.length; i++) {
            Object v = attr.getAttribute(props[i].getName());
            if (v instanceof String) {
                String value = (String)(String)v;
                Method writer = props[i].getWriteMethod();
                if (writer == null) {
                    return;
                }
                Class[] params = writer.getParameterTypes();
                if (params.length != 1) {
                    return;
                }
                String[] args = {value};
                try {
                    writer.invoke(comp, args);
                } catch (Exception ex) {
                    System.err.println("Invocation failed");
                }
            }
        }
    }
}
