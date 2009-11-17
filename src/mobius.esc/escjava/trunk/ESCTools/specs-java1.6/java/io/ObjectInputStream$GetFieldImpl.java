package java.io;

class ObjectInputStream$GetFieldImpl extends ObjectInputStream$GetField {
    /*synthetic*/ final ObjectInputStream this$0;
    private final ObjectStreamClass desc;
    private final byte[] primVals;
    private final Object[] objVals;
    private final int[] objHandles;
    
    ObjectInputStream$GetFieldImpl(/*synthetic*/ final ObjectInputStream this$0, ObjectStreamClass desc) {
        this.this$0 = this$0;
        
        this.desc = desc;
        primVals = new byte[desc.getPrimDataSize()];
        objVals = new Object[desc.getNumObjFields()];
        objHandles = new int[objVals.length];
    }
    
    public ObjectStreamClass getObjectStreamClass() {
        return desc;
    }
    
    public boolean defaulted(String name) throws IOException {
        return (getFieldOffset(name, null) < 0);
    }
    
    public boolean get(String name, boolean val) throws IOException {
        int off = getFieldOffset(name, Boolean.TYPE);
        return (off >= 0) ? Bits.getBoolean(primVals, off) : val;
    }
    
    public byte get(String name, byte val) throws IOException {
        int off = getFieldOffset(name, Byte.TYPE);
        return (off >= 0) ? primVals[off] : val;
    }
    
    public char get(String name, char val) throws IOException {
        int off = getFieldOffset(name, Character.TYPE);
        return (off >= 0) ? Bits.getChar(primVals, off) : val;
    }
    
    public short get(String name, short val) throws IOException {
        int off = getFieldOffset(name, Short.TYPE);
        return (off >= 0) ? Bits.getShort(primVals, off) : val;
    }
    
    public int get(String name, int val) throws IOException {
        int off = getFieldOffset(name, Integer.TYPE);
        return (off >= 0) ? Bits.getInt(primVals, off) : val;
    }
    
    public float get(String name, float val) throws IOException {
        int off = getFieldOffset(name, Float.TYPE);
        return (off >= 0) ? Bits.getFloat(primVals, off) : val;
    }
    
    public long get(String name, long val) throws IOException {
        int off = getFieldOffset(name, Long.TYPE);
        return (off >= 0) ? Bits.getLong(primVals, off) : val;
    }
    
    public double get(String name, double val) throws IOException {
        int off = getFieldOffset(name, Double.TYPE);
        return (off >= 0) ? Bits.getDouble(primVals, off) : val;
    }
    
    public Object get(String name, Object val) throws IOException {
        int off = getFieldOffset(name, Object.class);
        if (off >= 0) {
            int objHandle = objHandles[off];
            ObjectInputStream.access$100(this$0).markDependency(ObjectInputStream.access$000(this$0), objHandle);
            return (ObjectInputStream.access$100(this$0).lookupException(objHandle) == null) ? objVals[off] : null;
        } else {
            return val;
        }
    }
    
    void readFields() throws IOException {
        ObjectInputStream.access$200(this$0).readFully(primVals, 0, primVals.length, false);
        int oldHandle = ObjectInputStream.access$000(this$0);
        ObjectStreamField[] fields = desc.getFields(false);
        int numPrimFields = fields.length - objVals.length;
        for (int i = 0; i < objVals.length; i++) {
            objVals[i] = ObjectInputStream.access$300(this$0, fields[numPrimFields + i].isUnshared());
            objHandles[i] = ObjectInputStream.access$000(this$0);
        }
        ObjectInputStream.access$002(this$0, oldHandle);
    }
    
    private int getFieldOffset(String name, Class type) {
        ObjectStreamField field = desc.getField(name, type);
        if (field != null) {
            return field.getOffset();
        } else if (desc.getLocalDesc().getField(name, type) != null) {
            return -1;
        } else {
            throw new IllegalArgumentException("no such field");
        }
    }
}
