package java.beans;

class java_awt_Menu_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    java_awt_Menu_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        super.initialize(type, oldInstance, newInstance, out);
        java.awt.Menu m = (java.awt.Menu)(java.awt.Menu)oldInstance;
        java.awt.Menu n = (java.awt.Menu)(java.awt.Menu)newInstance;
        for (int i = n.getItemCount(); i < m.getItemCount(); i++) {
            invokeStatement(oldInstance, "add", new Object[]{m.getItem(i)}, out);
        }
    }
}
