package java.io;

class ObjectInputStream$ValidationList$Callback {
    final ObjectInputValidation obj;
    final int priority;
    ObjectInputStream$ValidationList$Callback next;
    
    ObjectInputStream$ValidationList$Callback(ObjectInputValidation obj, int priority, ObjectInputStream$ValidationList$Callback next) {
        
        this.obj = obj;
        this.priority = priority;
        this.next = next;
    }
}
