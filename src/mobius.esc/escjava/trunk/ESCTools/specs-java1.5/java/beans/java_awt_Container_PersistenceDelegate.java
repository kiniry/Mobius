package java.beans;

class java_awt_Container_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    java_awt_Container_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        super.initialize(type, oldInstance, newInstance, out);
        if (oldInstance instanceof javax.swing.JScrollPane) {
            return;
        }
        java.awt.Container oldC = (java.awt.Container)(.java.awt.Container)oldInstance;
        java.awt.Component[] oldChildren = oldC.getComponents();
        java.awt.Container newC = (java.awt.Container)(.java.awt.Container)newInstance;
        java.awt.Component[] newChildren = (newC == null) ? new java.awt.Component[0] : newC.getComponents();
        for (int i = newChildren.length; i < oldChildren.length; i++) {
            invokeStatement(oldInstance, "add", new Object[]{oldChildren[i]}, out);
        }
    }
}
