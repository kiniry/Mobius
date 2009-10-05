package java.beans;

class javax_swing_JFrame_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    javax_swing_JFrame_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        super.initialize(type, oldInstance, newInstance, out);
        java.awt.Window oldC = (java.awt.Window)(java.awt.Window)oldInstance;
        java.awt.Window newC = (java.awt.Window)(java.awt.Window)newInstance;
        boolean oldV = oldC.isVisible();
        boolean newV = newC.isVisible();
        if (newV != oldV) {
            boolean executeStatements = out.executeStatements;
            out.executeStatements = false;
            invokeStatement(oldInstance, "setVisible", new Object[]{Boolean.valueOf(oldV)}, out);
            out.executeStatements = executeStatements;
        }
    }
}
