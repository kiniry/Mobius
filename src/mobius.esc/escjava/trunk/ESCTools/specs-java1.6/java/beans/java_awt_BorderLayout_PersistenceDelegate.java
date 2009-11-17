package java.beans;

class java_awt_BorderLayout_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    java_awt_BorderLayout_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        super.initialize(type, oldInstance, newInstance, out);
        String[] locations = {"north", "south", "east", "west", "center"};
        String[] names = {java.awt.BorderLayout.NORTH, java.awt.BorderLayout.SOUTH, java.awt.BorderLayout.EAST, java.awt.BorderLayout.WEST, java.awt.BorderLayout.CENTER};
        for (int i = 0; i < locations.length; i++) {
            Object oldC = ReflectionUtils.getPrivateField(oldInstance, java.awt.BorderLayout.class, locations[i], out.getExceptionListener());
            Object newC = ReflectionUtils.getPrivateField(newInstance, java.awt.BorderLayout.class, locations[i], out.getExceptionListener());
            if (oldC != null && newC == null) {
                invokeStatement(oldInstance, "addLayoutComponent", new Object[]{oldC, names[i]}, out);
            }
        }
    }
}
