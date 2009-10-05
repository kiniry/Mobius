package java.beans;

class java_util_Map_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    java_util_Map_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        java.util.Map oldMap = (java.util.Map)(java.util.Map)oldInstance;
        java.util.Map newMap = (java.util.Map)(java.util.Map)newInstance;
        if (newMap != null) {
            java.util.Iterator newKeys = newMap.keySet().iterator();
            while (newKeys.hasNext()) {
                Object newKey = newKeys.next();
                if (!oldMap.containsKey(newKey)) {
                    invokeStatement(oldInstance, "remove", new Object[]{newKey}, out);
                }
            }
        }
        java.util.Iterator oldKeys = oldMap.keySet().iterator();
        while (oldKeys.hasNext()) {
            Object oldKey = oldKeys.next();
            Expression oldGetExp = new Expression(oldInstance, "get", new Object[]{oldKey});
            Expression newGetExp = new Expression(newInstance, "get", new Object[]{oldKey});
            try {
                Object oldValue = oldGetExp.getValue();
                Object newValue = newGetExp.getValue();
                out.writeExpression(oldGetExp);
                if (!MetaData.equals(newValue, out.get(oldValue))) {
                    invokeStatement(oldInstance, "put", new Object[]{oldKey, oldValue}, out);
                }
            } catch (Exception e) {
                out.getExceptionListener().exceptionThrown(e);
            }
        }
    }
}
