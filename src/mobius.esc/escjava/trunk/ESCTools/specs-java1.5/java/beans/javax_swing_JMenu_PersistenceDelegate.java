package java.beans;

class javax_swing_JMenu_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    javax_swing_JMenu_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        super.initialize(type, oldInstance, newInstance, out);
        javax.swing.JMenu m = (javax.swing.JMenu)(.javax.swing.JMenu)oldInstance;
        java.awt.Component[] c = m.getMenuComponents();
        for (int i = 0; i < c.length; i++) {
            invokeStatement(oldInstance, "add", new Object[]{c[i]}, out);
        }
    }
}
