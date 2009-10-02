package java.beans;

class javax_swing_Box_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    javax_swing_Box_PersistenceDelegate() {
        
    }
    
    protected Expression instantiate(Object oldInstance, Encoder out) {
        javax.swing.BoxLayout lm = (javax.swing.BoxLayout)(.javax.swing.BoxLayout)((javax.swing.Box)(.javax.swing.Box)oldInstance).getLayout();
        Object value = ReflectionUtils.getPrivateField(lm, .javax.swing.BoxLayout.class, "axis", out.getExceptionListener());
        String method = ((Integer)(Integer)value).intValue() == javax.swing.BoxLayout.X_AXIS ? "createHorizontalBox" : "createVerticalBox";
        return new Expression(oldInstance, oldInstance.getClass(), method, new Object[0]);
    }
}
