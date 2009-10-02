package java.io;

class ObjectOutputStream$PutFieldImpl extends ObjectOutputStream$PutField {
    /*synthetic*/ final ObjectOutputStream this$0;
    private final ObjectStreamClass desc;
    private final byte[] primVals;
    private final Object[] objVals;
    
    ObjectOutputStream$PutFieldImpl(/*synthetic*/ final ObjectOutputStream this$0, ObjectStreamClass desc) {
        this.this$0 = this$0;
        
        this.desc = desc;
        primVals = new byte[desc.getPrimDataSize()];
        objVals = new Object[desc.getNumObjFields()];
    }
    
    public void put(String name, boolean val) {
        Bits.putBoolean(primVals, getFieldOffset(name, Boolean.TYPE), val);
    }
    
    public void put(String name, byte val) {
        primVals[getFieldOffset(name, Byte.TYPE)] = val;
    }
    
    public void put(String name, char val) {
        Bits.putChar(primVals, getFieldOffset(name, Character.TYPE), val);
    }
    
    public void put(String name, short val) {
        Bits.putShort(primVals, getFieldOffset(name, Short.TYPE), val);
    }
    
    public void put(String name, int val) {
        Bits.putInt(primVals, getFieldOffset(name, Integer.TYPE), val);
    }
    
    public void put(String name, float val) {
        Bits.putFloat(primVals, getFieldOffset(name, Float.TYPE), val);
    }
    
    public void put(String name, long val) {
        Bits.putLong(primVals, getFieldOffset(name, Long.TYPE), val);
    }
    
    public void put(String name, double val) {
        Bits.putDouble(primVals, getFieldOffset(name, Double.TYPE), val);
    }
    
    public void put(String name, Object val) {
        objVals[getFieldOffset(name, Object.class)] = val;
    }
    
    public void write(ObjectOutput out) throws IOException {
        if (this$0 != out) {
            throw new IllegalArgumentException("wrong stream");
        }
        out.write(primVals, 0, primVals.length);
        ObjectStreamField[] fields = desc.getFields(false);
        int numPrimFields = fields.length - objVals.length;
        for (int i = 0; i < objVals.length; i++) {
            if (fields[numPrimFields + i].isUnshared()) {
                throw new IOException("cannot write unshared object");
            }
            out.writeObject(objVals[i]);
        }
    }
    
    void writeFields() throws IOException {
        ObjectOutputStream.access$000(this$0).write(primVals, 0, primVals.length, false);
        ObjectStreamField[] fields = desc.getFields(false);
        int numPrimFields = fields.length - objVals.length;
        for (int i = 0; i < objVals.length; i++) {
            ObjectOutputStream.access$100(this$0, objVals[i], fields[numPrimFields + i].isUnshared());
        }
    }
    
    private int getFieldOffset(String name, Class type) {
        ObjectStreamField field = desc.getField(name, type);
        if (field == null) {
            throw new IllegalArgumentException("no such field");
        }
        return field.getOffset();
    }
}
