package java.beans;

class java_awt_MenuShortcut_PersistenceDelegate extends PersistenceDelegate {
    
    java_awt_MenuShortcut_PersistenceDelegate() {
        
    }
    
    protected Expression instantiate(Object oldInstance, Encoder out) {
        java.awt.MenuShortcut m = (java.awt.MenuShortcut)(java.awt.MenuShortcut)oldInstance;
        return new Expression(oldInstance, m.getClass(), "new", new Object[]{new Integer(m.getKey()), Boolean.valueOf(m.usesShiftModifier())});
    }
}
