package java.beans;

class java_awt_List_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    java_awt_List_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        super.initialize(type, oldInstance, newInstance, out);
        java.awt.List m = (java.awt.List)(java.awt.List)oldInstance;
        java.awt.List n = (java.awt.List)(java.awt.List)newInstance;
        for (int i = n.getItemCount(); i < m.getItemCount(); i++) {
            invokeStatement(oldInstance, "add", new Object[]{m.getItem(i)}, out);
        }
    }
}
