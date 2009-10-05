package java.beans;

import java.util.Hashtable;
import java.util.Enumeration;

class java_awt_GridBagLayout_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    java_awt_GridBagLayout_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        super.initialize(type, oldInstance, newInstance, out);
        Hashtable comptable = (Hashtable)(Hashtable)ReflectionUtils.getPrivateField(oldInstance, java.awt.GridBagLayout.class, "comptable", out.getExceptionListener());
        if (comptable != null) {
            for (Enumeration e = comptable.keys(); e.hasMoreElements(); ) {
                Object child = e.nextElement();
                invokeStatement(oldInstance, "addLayoutComponent", new Object[]{child, comptable.get(child)}, out);
            }
        }
    }
}
