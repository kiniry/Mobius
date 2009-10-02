package java.beans;

import java.util.Hashtable;
import java.util.Enumeration;

class java_awt_CardLayout_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    java_awt_CardLayout_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        super.initialize(type, oldInstance, newInstance, out);
        Hashtable tab = (Hashtable)(Hashtable)ReflectionUtils.getPrivateField(oldInstance, .java.awt.CardLayout.class, "tab", out.getExceptionListener());
        if (tab != null) {
            for (Enumeration e = tab.keys(); e.hasMoreElements(); ) {
                Object child = e.nextElement();
                invokeStatement(oldInstance, "addLayoutComponent", new Object[]{child, (String)(String)tab.get(child)}, out);
            }
        }
    }
}
