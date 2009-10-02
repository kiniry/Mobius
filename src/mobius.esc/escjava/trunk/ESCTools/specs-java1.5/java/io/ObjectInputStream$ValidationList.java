package java.io;

class ObjectInputStream$ValidationList {
    {
    }
    private ObjectInputStream$ValidationList$Callback list;
    
    ObjectInputStream$ValidationList() {
        
    }
    
    void register(ObjectInputValidation obj, int priority) throws InvalidObjectException {
        if (obj == null) {
            throw new InvalidObjectException("null callback");
        }
        ObjectInputStream$ValidationList$Callback prev = null;
        ObjectInputStream$ValidationList$Callback cur = list;
        while (cur != null && priority < cur.priority) {
            prev = cur;
            cur = cur.next;
        }
        if (prev != null) {
            prev.next = new ObjectInputStream$ValidationList$Callback(obj, priority, cur);
        } else {
            list = new ObjectInputStream$ValidationList$Callback(obj, priority, list);
        }
    }
    
    void doCallbacks() throws InvalidObjectException {
        try {
            while (list != null) {
                list.obj.validateObject();
                list = list.next;
            }
        } catch (InvalidObjectException ex) {
            list = null;
            throw ex;
        }
    }
    
    public void clear() {
        list = null;
    }
}
