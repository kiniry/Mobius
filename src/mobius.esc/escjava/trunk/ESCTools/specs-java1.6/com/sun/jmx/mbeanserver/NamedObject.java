package com.sun.jmx.mbeanserver;

import javax.management.*;

public class NamedObject {
    private ObjectName name;
    private Object object = null;
    
    public NamedObject(ObjectName objectName, Object object) {
        
        if (objectName.isPattern()) {
            throw new RuntimeOperationsException(new IllegalArgumentException("Invalid name->" + objectName.toString()));
        }
        this.name = objectName;
        this.object = object;
    }
    
    public NamedObject(String objectName, Object object) throws MalformedObjectNameException {
        
        ObjectName objName = new ObjectName(objectName);
        if (objName.isPattern()) {
            throw new RuntimeOperationsException(new IllegalArgumentException("Invalid name->" + objName.toString()));
        }
        this.name = objName;
        this.object = object;
    }
    
    public boolean equals(Object object) {
        if (this == object) return true;
        if (object == null) return false;
        if (!(object instanceof NamedObject)) return false;
        NamedObject no = (NamedObject)(NamedObject)object;
        return name.equals(no.getName());
    }
    
    public int hashCode() {
        return name.hashCode();
    }
    
    public ObjectName getName() {
        return name;
    }
    
    public Object getObject() {
        return object;
    }
}
