package com.sun.jmx.mbeanserver;

import java.util.ArrayList;
import java.util.Set;
import javax.management.*;

public interface Repository {
    
    public void setConfigParameters(ArrayList configParameters);
    
    public boolean isFiltering();
    
    public void addMBean(Object object, ObjectName name) throws InstanceAlreadyExistsException;
    
    public boolean contains(ObjectName name);
    
    public Object retrieve(ObjectName name);
    
    public Set query(ObjectName name, QueryExp query);
    
    public void remove(ObjectName name) throws InstanceNotFoundException;
    
    public Integer getCount();
    
    public String getDefaultDomain();
    
    public String[] getDomains();
}
