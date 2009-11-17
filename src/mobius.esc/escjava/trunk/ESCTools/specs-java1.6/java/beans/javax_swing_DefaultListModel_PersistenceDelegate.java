package java.beans;

class javax_swing_DefaultListModel_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    javax_swing_DefaultListModel_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        super.initialize(type, oldInstance, newInstance, out);
        javax.swing.DefaultListModel m = (javax.swing.DefaultListModel)(javax.swing.DefaultListModel)oldInstance;
        javax.swing.DefaultListModel n = (javax.swing.DefaultListModel)(javax.swing.DefaultListModel)newInstance;
        for (int i = n.getSize(); i < m.getSize(); i++) {
            invokeStatement(oldInstance, "add", new Object[]{m.getElementAt(i)}, out);
        }
    }
}
