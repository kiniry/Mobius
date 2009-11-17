package java.io;

import java.util.concurrent.atomic.AtomicBoolean;

class ObjectInputStream$CallbackContext {
    private final Object obj;
    private final ObjectStreamClass desc;
    private final AtomicBoolean used = new AtomicBoolean();
    
    public ObjectInputStream$CallbackContext(Object obj, ObjectStreamClass desc) {
        
        this.obj = obj;
        this.desc = desc;
    }
    
    public Object getObj() throws NotActiveException {
        checkAndSetUsed();
        return obj;
    }
    
    public ObjectStreamClass getDesc() {
        return desc;
    }
    
    private void checkAndSetUsed() throws NotActiveException {
        if (!used.compareAndSet(false, true)) {
            throw new NotActiveException("not in readObject invocation or fields already read");
        }
    }
    
    public void setUsed() {
        used.set(true);
    }
}
