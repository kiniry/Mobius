package java.io;

import java.lang.reflect.Field;
import java.util.ArrayList;
import sun.misc.Unsafe;

class ObjectStreamClass$FieldReflector {
    private static final Unsafe unsafe = Unsafe.getUnsafe();
    private final ObjectStreamField[] fields;
    private final int numPrimFields;
    private final long[] keys;
    private final int[] offsets;
    private final char[] typeCodes;
    private final Class[] types;
    
    ObjectStreamClass$FieldReflector(ObjectStreamField[] fields) {
        
        this.fields = fields;
        int nfields = fields.length;
        keys = new long[nfields];
        offsets = new int[nfields];
        typeCodes = new char[nfields];
        ArrayList typeList = new ArrayList();
        for (int i = 0; i < nfields; i++) {
            ObjectStreamField f = fields[i];
            Field rf = f.getField();
            keys[i] = (rf != null) ? unsafe.objectFieldOffset(rf) : Unsafe.INVALID_FIELD_OFFSET;
            offsets[i] = f.getOffset();
            typeCodes[i] = f.getTypeCode();
            if (!f.isPrimitive()) {
                typeList.add((rf != null) ? rf.getType() : null);
            }
        }
        types = (Class[])(Class[])typeList.toArray(new Class[typeList.size()]);
        numPrimFields = nfields - types.length;
    }
    
    ObjectStreamField[] getFields() {
        return fields;
    }
    
    void getPrimFieldValues(Object obj, byte[] buf) {
        if (obj == null) {
            throw new NullPointerException();
        }
        for (int i = 0; i < numPrimFields; i++) {
            long key = keys[i];
            int off = offsets[i];
            switch (typeCodes[i]) {
            case 'Z': 
                Bits.putBoolean(buf, off, unsafe.getBoolean(obj, key));
                break;
            
            case 'B': 
                buf[off] = unsafe.getByte(obj, key);
                break;
            
            case 'C': 
                Bits.putChar(buf, off, unsafe.getChar(obj, key));
                break;
            
            case 'S': 
                Bits.putShort(buf, off, unsafe.getShort(obj, key));
                break;
            
            case 'I': 
                Bits.putInt(buf, off, unsafe.getInt(obj, key));
                break;
            
            case 'F': 
                Bits.putFloat(buf, off, unsafe.getFloat(obj, key));
                break;
            
            case 'J': 
                Bits.putLong(buf, off, unsafe.getLong(obj, key));
                break;
            
            case 'D': 
                Bits.putDouble(buf, off, unsafe.getDouble(obj, key));
                break;
            
            default: 
                throw new InternalError();
            
            }
        }
    }
    
    void setPrimFieldValues(Object obj, byte[] buf) {
        if (obj == null) {
            throw new NullPointerException();
        }
        for (int i = 0; i < numPrimFields; i++) {
            long key = keys[i];
            if (key == Unsafe.INVALID_FIELD_OFFSET) {
                continue;
            }
            int off = offsets[i];
            switch (typeCodes[i]) {
            case 'Z': 
                unsafe.putBoolean(obj, key, Bits.getBoolean(buf, off));
                break;
            
            case 'B': 
                unsafe.putByte(obj, key, buf[off]);
                break;
            
            case 'C': 
                unsafe.putChar(obj, key, Bits.getChar(buf, off));
                break;
            
            case 'S': 
                unsafe.putShort(obj, key, Bits.getShort(buf, off));
                break;
            
            case 'I': 
                unsafe.putInt(obj, key, Bits.getInt(buf, off));
                break;
            
            case 'F': 
                unsafe.putFloat(obj, key, Bits.getFloat(buf, off));
                break;
            
            case 'J': 
                unsafe.putLong(obj, key, Bits.getLong(buf, off));
                break;
            
            case 'D': 
                unsafe.putDouble(obj, key, Bits.getDouble(buf, off));
                break;
            
            default: 
                throw new InternalError();
            
            }
        }
    }
    
    void getObjFieldValues(Object obj, Object[] vals) {
        if (obj == null) {
            throw new NullPointerException();
        }
        for (int i = numPrimFields; i < fields.length; i++) {
            switch (typeCodes[i]) {
            case 'L': 
            
            case '[': 
                vals[offsets[i]] = unsafe.getObject(obj, keys[i]);
                break;
            
            default: 
                throw new InternalError();
            
            }
        }
    }
    
    void setObjFieldValues(Object obj, Object[] vals) {
        if (obj == null) {
            throw new NullPointerException();
        }
        for (int i = numPrimFields; i < fields.length; i++) {
            long key = keys[i];
            if (key == Unsafe.INVALID_FIELD_OFFSET) {
                continue;
            }
            switch (typeCodes[i]) {
            case 'L': 
            
            case '[': 
                Object val = vals[offsets[i]];
                if (val != null && !types[i - numPrimFields].isInstance(val)) {
                    Field f = fields[i].getField();
                    throw new ClassCastException("cannot assign instance of " + val.getClass().getName() + " to field " + f.getDeclaringClass().getName() + "." + f.getName() + " of type " + f.getType().getName() + " in instance of " + obj.getClass().getName());
                }
                unsafe.putObject(obj, key, val);
                break;
            
            default: 
                throw new InternalError();
            
            }
        }
    }
}
