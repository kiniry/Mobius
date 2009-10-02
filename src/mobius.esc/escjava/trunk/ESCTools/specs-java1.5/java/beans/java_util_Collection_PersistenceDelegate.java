package java.beans;

import java.util.Iterator;

class java_util_Collection_PersistenceDelegate extends DefaultPersistenceDelegate {
    
    java_util_Collection_PersistenceDelegate() {
        
    }
    
    protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
        java.util.Collection oldO = (java.util.Collection)(.java.util.Collection)oldInstance;
        java.util.Collection newO = (java.util.Collection)(.java.util.Collection)newInstance;
        if (newO.size() != 0) {
            invokeStatement(oldInstance, "clear", new Object[]{}, out);
        }
        for (Iterator i = oldO.iterator(); i.hasNext(); ) {
            invokeStatement(oldInstance, "add", new Object[]{i.next()}, out);
        }
    }
}
