package java.beans;

class java_awt_Choice_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    java_awt_Choice_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        super.initialize(type, oldInstance, newInstance, out);
        java.awt.Choice m = (java.awt.Choice)(.java.awt.Choice)oldInstance;
        java.awt.Choice n = (java.awt.Choice)(.java.awt.Choice)newInstance;
        for (int i = n.getItemCount(); i < m.getItemCount(); i++) {
            invokeStatement(oldInstance, "add", new Object[]{m.getItem(i)}, out);
        }
    }
}
