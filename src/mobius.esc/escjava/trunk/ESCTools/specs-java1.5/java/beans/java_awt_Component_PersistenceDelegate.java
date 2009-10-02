package java.beans;

class java_awt_Component_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    java_awt_Component_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        super.initialize(type, oldInstance, newInstance, out);
        java.awt.Component c = (java.awt.Component)(.java.awt.Component)oldInstance;
        java.awt.Component c2 = (java.awt.Component)(.java.awt.Component)newInstance;
        if (!(oldInstance instanceof java.awt.Window)) {
            String[] fieldNames = new String[]{"background", "foreground", "font"};
            for (int i = 0; i < fieldNames.length; i++) {
                String name = fieldNames[i];
                Object oldValue = ReflectionUtils.getPrivateField(oldInstance, .java.awt.Component.class, name, out.getExceptionListener());
                Object newValue = (newInstance == null) ? null : ReflectionUtils.getPrivateField(newInstance, .java.awt.Component.class, name, out.getExceptionListener());
                if (oldValue != null && !oldValue.equals(newValue)) {
                    invokeStatement(oldInstance, "set" + NameGenerator.capitalize(name), new Object[]{oldValue}, out);
                }
            }
        }
        java.awt.Container p = c.getParent();
        if (p == null || p.getLayout() == null && !(p instanceof javax.swing.JLayeredPane)) {
            boolean locationCorrect = c.getLocation().equals(c2.getLocation());
            boolean sizeCorrect = c.getSize().equals(c2.getSize());
            if (!locationCorrect && !sizeCorrect) {
                invokeStatement(oldInstance, "setBounds", new Object[]{c.getBounds()}, out);
            } else if (!locationCorrect) {
                invokeStatement(oldInstance, "setLocation", new Object[]{c.getLocation()}, out);
            } else if (!sizeCorrect) {
                invokeStatement(oldInstance, "setSize", new Object[]{c.getSize()}, out);
            }
        }
    }
}
