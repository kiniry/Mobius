package java.beans;

class java_awt_MenuBar_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    java_awt_MenuBar_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        super.initialize(type, oldInstance, newInstance, out);
        java.awt.MenuBar m = (java.awt.MenuBar)(.java.awt.MenuBar)oldInstance;
        java.awt.MenuBar n = (java.awt.MenuBar)(.java.awt.MenuBar)newInstance;
        for (int i = n.getMenuCount(); i < m.getMenuCount(); i++) {
            invokeStatement(oldInstance, "add", new Object[]{m.getMenu(i)}, out);
        }
    }
}
