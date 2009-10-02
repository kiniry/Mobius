package java.io;

import java.util.Arrays;

class ObjectInputStream$HandleTable {
    private static final byte STATUS_OK = 1;
    private static final byte STATUS_UNKNOWN = 2;
    private static final byte STATUS_EXCEPTION = 3;
    byte[] status;
    Object[] entries;
    ObjectInputStream$HandleTable$HandleList[] deps;
    int lowDep = -1;
    int size = 0;
    
    ObjectInputStream$HandleTable(int initialCapacity) {
        
        status = new byte[initialCapacity];
        entries = new Object[initialCapacity];
        deps = new ObjectInputStream$HandleTable$HandleList[initialCapacity];
    }
    
    int assign(Object obj) {
        if (size >= entries.length) {
            grow();
        }
        status[size] = STATUS_UNKNOWN;
        entries[size] = obj;
        return size++;
    }
    
    void markDependency(int dependent, int target) {
        if (dependent == -1 || target == -1) {
            return;
        }
        switch (status[dependent]) {
        case STATUS_UNKNOWN: 
            switch (status[target]) {
            case STATUS_OK: 
                break;
            
            case STATUS_EXCEPTION: 
                markException(dependent, (ClassNotFoundException)(ClassNotFoundException)entries[target]);
                break;
            
            case STATUS_UNKNOWN: 
                if (deps[target] == null) {
                    deps[target] = new ObjectInputStream$HandleTable$HandleList();
                }
                deps[target].add(dependent);
                if (lowDep < 0 || lowDep > target) {
                    lowDep = target;
                }
                break;
            
            default: 
                throw new InternalError();
            
            }
            break;
        
        case STATUS_EXCEPTION: 
            break;
        
        default: 
            throw new InternalError();
        
        }
    }
    
    void markException(int handle, ClassNotFoundException ex) {
        switch (status[handle]) {
        case STATUS_UNKNOWN: 
            status[handle] = STATUS_EXCEPTION;
            entries[handle] = ex;
            ObjectInputStream$HandleTable$HandleList dlist = deps[handle];
            if (dlist != null) {
                int ndeps = dlist.size();
                for (int i = 0; i < ndeps; i++) {
                    markException(dlist.get(i), ex);
                }
                deps[handle] = null;
            }
            break;
        
        case STATUS_EXCEPTION: 
            break;
        
        default: 
            throw new InternalError();
        
        }
    }
    
    void finish(int handle) {
        int end;
        if (lowDep < 0) {
            end = handle + 1;
        } else if (lowDep >= handle) {
            end = size;
            lowDep = -1;
        } else {
            return;
        }
        for (int i = handle; i < end; i++) {
            switch (status[i]) {
            case STATUS_UNKNOWN: 
                status[i] = STATUS_OK;
                deps[i] = null;
                break;
            
            case STATUS_OK: 
            
            case STATUS_EXCEPTION: 
                break;
            
            default: 
                throw new InternalError();
            
            }
        }
    }
    
    void setObject(int handle, Object obj) {
        switch (status[handle]) {
        case STATUS_UNKNOWN: 
        
        case STATUS_OK: 
            entries[handle] = obj;
            break;
        
        case STATUS_EXCEPTION: 
            break;
        
        default: 
            throw new InternalError();
        
        }
    }
    
    Object lookupObject(int handle) {
        return (handle != -1 && status[handle] != STATUS_EXCEPTION) ? entries[handle] : null;
    }
    
    ClassNotFoundException lookupException(int handle) {
        return (handle != -1 && status[handle] == STATUS_EXCEPTION) ? (ClassNotFoundException)(ClassNotFoundException)entries[handle] : null;
    }
    
    void clear() {
        Arrays.fill(status, 0, size, (byte)0);
        Arrays.fill(entries, 0, size, null);
        Arrays.fill(deps, 0, size, null);
        lowDep = -1;
        size = 0;
    }
    
    int size() {
        return size;
    }
    
    private void grow() {
        int newCapacity = (entries.length << 1) + 1;
        byte[] newStatus = new byte[newCapacity];
        Object[] newEntries = new Object[newCapacity];
        ObjectInputStream$HandleTable$HandleList[] newDeps = new ObjectInputStream$HandleTable$HandleList[newCapacity];
        System.arraycopy(status, 0, newStatus, 0, size);
        System.arraycopy(entries, 0, newEntries, 0, size);
        System.arraycopy(deps, 0, newDeps, 0, size);
        status = newStatus;
        entries = newEntries;
        deps = newDeps;
    }
    {
    }
}
