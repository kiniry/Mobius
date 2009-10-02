package java.beans;

class javax_swing_DefaultComboBoxModel_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    javax_swing_DefaultComboBoxModel_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        super.initialize(type, oldInstance, newInstance, out);
        javax.swing.DefaultComboBoxModel m = (javax.swing.DefaultComboBoxModel)(.javax.swing.DefaultComboBoxModel)oldInstance;
        for (int i = 0; i < m.getSize(); i++) {
            invokeStatement(oldInstance, "addElement", new Object[]{m.getElementAt(i)}, out);
        }
    }
}
