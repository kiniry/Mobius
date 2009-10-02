package java.beans;

class javax_swing_JTabbedPane_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    javax_swing_JTabbedPane_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        super.initialize(type, oldInstance, newInstance, out);
        javax.swing.JTabbedPane p = (javax.swing.JTabbedPane)(.javax.swing.JTabbedPane)oldInstance;
        for (int i = 0; i < p.getTabCount(); i++) {
            invokeStatement(oldInstance, "addTab", new Object[]{p.getTitleAt(i), p.getIconAt(i), p.getComponentAt(i)}, out);
        }
    }
}
