package java.io;

class ObjectStreamClass$ClassDataSlot {
    final ObjectStreamClass desc;
    final boolean hasData;
    
    ObjectStreamClass$ClassDataSlot(ObjectStreamClass desc, boolean hasData) {
        
        this.desc = desc;
        this.hasData = hasData;
    }
}
