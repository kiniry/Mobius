package java.beans;

class javax_swing_ToolTipManager_PersistenceDelegate extends PersistenceDelegate {
    
    javax_swing_ToolTipManager_PersistenceDelegate() {
        
    }
    
    protected Expression instantiate(Object oldInstance, Encoder out) {
        return new Expression(oldInstance, javax.swing.ToolTipManager.class, "sharedInstance", new Object[]{});
    }
}
