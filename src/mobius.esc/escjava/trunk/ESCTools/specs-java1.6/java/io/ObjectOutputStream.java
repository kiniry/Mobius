package java.io;

import java.io.ObjectStreamClass.WeakClassKey;
import java.security.AccessController;

public class ObjectOutputStream extends OutputStream implements ObjectOutput, ObjectStreamConstants {
    
    /*synthetic*/ static void access$300(double[] x0, int x1, byte[] x2, int x3, int x4) {
        doublesToBytes(x0, x1, x2, x3, x4);
    }
    
    /*synthetic*/ static void access$200(float[] x0, int x1, byte[] x2, int x3, int x4) {
        floatsToBytes(x0, x1, x2, x3, x4);
    }
    
    /*synthetic*/ static void access$100(ObjectOutputStream x0, Object x1, boolean x2) throws IOException {
        x0.writeObject0(x1, x2);
    }
    
    /*synthetic*/ static ObjectOutputStream$BlockDataOutputStream access$000(ObjectOutputStream x0) {
        return x0.bout;
    }
    {
    }
    private final ObjectOutputStream$BlockDataOutputStream bout;
    private final ObjectOutputStream$HandleTable handles;
    private final ObjectOutputStream$ReplaceTable subs;
    private int protocol = PROTOCOL_VERSION_2;
    private int depth;
    private byte[] primVals;
    private final boolean enableOverride;
    private boolean enableReplace;
    private Object curObj;
    private ObjectStreamClass curDesc;
    private ObjectOutputStream$PutFieldImpl curPut;
    
    public ObjectOutputStream(OutputStream out) throws IOException {
        
        verifySubclass();
        bout = new ObjectOutputStream$BlockDataOutputStream(out);
        handles = new ObjectOutputStream$HandleTable(10, (float)3.0);
        subs = new ObjectOutputStream$ReplaceTable(10, (float)3.0);
        enableOverride = false;
        writeStreamHeader();
        bout.setBlockDataMode(true);
    }
    
    protected ObjectOutputStream() throws IOException, SecurityException {
        
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(SUBCLASS_IMPLEMENTATION_PERMISSION);
        }
        bout = null;
        handles = null;
        subs = null;
        enableOverride = true;
    }
    
    public void useProtocolVersion(int version) throws IOException {
        if (handles.size() != 0) {
            throw new IllegalStateException("stream non-empty");
        }
        switch (version) {
        case PROTOCOL_VERSION_1: 
        
        case PROTOCOL_VERSION_2: 
            protocol = version;
            break;
        
        default: 
            throw new IllegalArgumentException("unknown version: " + version);
        
        }
    }
    
    public final void writeObject(Object obj) throws IOException {
        if (enableOverride) {
            writeObjectOverride(obj);
            return;
        }
        try {
            writeObject0(obj, false);
        } catch (IOException ex) {
            if (depth == 0) {
                writeFatalException(ex);
            }
            throw ex;
        }
    }
    
    protected void writeObjectOverride(Object obj) throws IOException {
    }
    
    public void writeUnshared(Object obj) throws IOException {
        try {
            writeObject0(obj, true);
        } catch (IOException ex) {
            if (depth == 0) {
                writeFatalException(ex);
            }
            throw ex;
        }
    }
    
    public void defaultWriteObject() throws IOException {
        if (curObj == null || curDesc == null) {
            throw new NotActiveException("not in call to writeObject");
        }
        bout.setBlockDataMode(false);
        defaultWriteFields(curObj, curDesc);
        bout.setBlockDataMode(true);
    }
    
    public ObjectOutputStream$PutField putFields() throws IOException {
        if (curPut == null) {
            if (curObj == null || curDesc == null) {
                throw new NotActiveException("not in call to writeObject");
            }
            curPut = new ObjectOutputStream$PutFieldImpl(this, curDesc);
        }
        return curPut;
    }
    
    public void writeFields() throws IOException {
        if (curPut == null) {
            throw new NotActiveException("no current PutField object");
        }
        bout.setBlockDataMode(false);
        curPut.writeFields();
        bout.setBlockDataMode(true);
    }
    
    public void reset() throws IOException {
        if (depth != 0) {
            throw new IOException("stream active");
        }
        bout.setBlockDataMode(false);
        bout.writeByte(TC_RESET);
        clear();
        bout.setBlockDataMode(true);
    }
    
    protected void annotateClass(Class cl) throws IOException {
    }
    
    protected void annotateProxyClass(Class cl) throws IOException {
    }
    
    protected Object replaceObject(Object obj) throws IOException {
        return obj;
    }
    
    protected boolean enableReplaceObject(boolean enable) throws SecurityException {
        if (enable == enableReplace) {
            return enable;
        }
        if (enable) {
            SecurityManager sm = System.getSecurityManager();
            if (sm != null) {
                sm.checkPermission(SUBSTITUTION_PERMISSION);
            }
        }
        enableReplace = enable;
        return !enableReplace;
    }
    
    protected void writeStreamHeader() throws IOException {
        bout.writeShort(STREAM_MAGIC);
        bout.writeShort(STREAM_VERSION);
    }
    
    protected void writeClassDescriptor(ObjectStreamClass desc) throws IOException {
        desc.writeNonProxy(this);
    }
    
    public void write(int val) throws IOException {
        bout.write(val);
    }
    
    public void write(byte[] buf) throws IOException {
        bout.write(buf, 0, buf.length, false);
    }
    
    public void write(byte[] buf, int off, int len) throws IOException {
        if (buf == null) {
            throw new NullPointerException();
        }
        int endoff = off + len;
        if (off < 0 || len < 0 || endoff > buf.length || endoff < 0) {
            throw new IndexOutOfBoundsException();
        }
        bout.write(buf, off, len, false);
    }
    
    public void flush() throws IOException {
        bout.flush();
    }
    
    protected void drain() throws IOException {
        bout.drain();
    }
    
    public void close() throws IOException {
        flush();
        clear();
        bout.close();
    }
    
    public void writeBoolean(boolean val) throws IOException {
        bout.writeBoolean(val);
    }
    
    public void writeByte(int val) throws IOException {
        bout.writeByte(val);
    }
    
    public void writeShort(int val) throws IOException {
        bout.writeShort(val);
    }
    
    public void writeChar(int val) throws IOException {
        bout.writeChar(val);
    }
    
    public void writeInt(int val) throws IOException {
        bout.writeInt(val);
    }
    
    public void writeLong(long val) throws IOException {
        bout.writeLong(val);
    }
    
    public void writeFloat(float val) throws IOException {
        bout.writeFloat(val);
    }
    
    public void writeDouble(double val) throws IOException {
        bout.writeDouble(val);
    }
    
    public void writeBytes(String str) throws IOException {
        bout.writeBytes(str);
    }
    
    public void writeChars(String str) throws IOException {
        bout.writeChars(str);
    }
    
    public void writeUTF(String str) throws IOException {
        bout.writeUTF(str);
    }
    {
    }
    
    int getProtocolVersion() {
        return protocol;
    }
    
    void writeTypeString(String str) throws IOException {
        int handle;
        if (str == null) {
            writeNull();
        } else if ((handle = handles.lookup(str)) != -1) {
            writeHandle(handle);
        } else {
            writeString(str, false);
        }
    }
    
    private void verifySubclass() {
        Class cl = getClass();
        ObjectStreamClass.processQueue(ObjectOutputStream$Caches.subclassAuditsQueue, ObjectOutputStream$Caches.subclassAudits);
        ObjectStreamClass$WeakClassKey key = new ObjectStreamClass$WeakClassKey(cl, ObjectOutputStream$Caches.subclassAuditsQueue);
        Boolean result = (Boolean)ObjectOutputStream$Caches.subclassAudits.get(key);
        if (result == null) {
            result = Boolean.valueOf(auditSubclass(cl));
            ObjectOutputStream$Caches.subclassAudits.putIfAbsent(key, result);
        }
        if (result.booleanValue()) {
            return;
        }
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(SUBCLASS_IMPLEMENTATION_PERMISSION);
        }
    }
    
    private static boolean auditSubclass(final Class subcl) {
        Boolean result = (Boolean)(Boolean)AccessController.doPrivileged(new ObjectOutputStream$1(subcl));
        return result.booleanValue();
    }
    
    private void clear() {
        subs.clear();
        handles.clear();
    }
    
    private void writeObject0(Object obj, boolean unshared) throws IOException {
        boolean oldMode = bout.setBlockDataMode(false);
        depth++;
        try {
            int h;
            if ((obj = subs.lookup(obj)) == null) {
                writeNull();
                return;
            } else if (!unshared && (h = handles.lookup(obj)) != -1) {
                writeHandle(h);
                return;
            } else if (obj instanceof Class) {
                writeClass((Class)(Class)obj, unshared);
                return;
            } else if (obj instanceof ObjectStreamClass) {
                writeClassDesc((ObjectStreamClass)(ObjectStreamClass)obj, unshared);
                return;
            }
            Object orig = obj;
            Class cl = obj.getClass();
            ObjectStreamClass desc;
            for (; ; ) {
                Class repCl;
                desc = ObjectStreamClass.lookup(cl, true);
                if (!desc.hasWriteReplaceMethod() || (obj = desc.invokeWriteReplace(obj)) == null || (repCl = obj.getClass()) == cl) {
                    break;
                }
                cl = repCl;
            }
            if (enableReplace) {
                Object r = replaceObject(obj);
                if (r != obj && r != null) {
                    cl = r.getClass();
                    desc = ObjectStreamClass.lookup(cl, true);
                }
                obj = r;
            }
            if (obj != orig) {
                subs.assign(orig, obj);
                if (obj == null) {
                    writeNull();
                    return;
                } else if (!unshared && (h = handles.lookup(obj)) != -1) {
                    writeHandle(h);
                    return;
                } else if (obj instanceof Class) {
                    writeClass((Class)(Class)obj, unshared);
                    return;
                } else if (obj instanceof ObjectStreamClass) {
                    writeClassDesc((ObjectStreamClass)(ObjectStreamClass)obj, unshared);
                    return;
                }
            }
            if (obj instanceof String) {
                writeString((String)(String)obj, unshared);
            } else if (cl.isArray()) {
                writeArray(obj, desc, unshared);
            } else if (obj instanceof Enum) {
                writeEnum((Enum)(Enum)obj, desc, unshared);
            } else if (obj instanceof Serializable) {
                writeOrdinaryObject(obj, desc, unshared);
            } else {
                throw new NotSerializableException(cl.getName());
            }
        } finally {
            depth--;
            bout.setBlockDataMode(oldMode);
        }
    }
    
    private void writeNull() throws IOException {
        bout.writeByte(TC_NULL);
    }
    
    private void writeHandle(int handle) throws IOException {
        bout.writeByte(TC_REFERENCE);
        bout.writeInt(baseWireHandle + handle);
    }
    
    private void writeClass(Class cl, boolean unshared) throws IOException {
        bout.writeByte(TC_CLASS);
        writeClassDesc(ObjectStreamClass.lookup(cl, true), false);
        handles.assign(unshared ? null : cl);
    }
    
    private void writeClassDesc(ObjectStreamClass desc, boolean unshared) throws IOException {
        int handle;
        if (desc == null) {
            writeNull();
        } else if (!unshared && (handle = handles.lookup(desc)) != -1) {
            writeHandle(handle);
        } else if (desc.isProxy()) {
            writeProxyDesc(desc, unshared);
        } else {
            writeNonProxyDesc(desc, unshared);
        }
    }
    
    private void writeProxyDesc(ObjectStreamClass desc, boolean unshared) throws IOException {
        bout.writeByte(TC_PROXYCLASSDESC);
        handles.assign(unshared ? null : desc);
        Class cl = desc.forClass();
        Class[] ifaces = cl.getInterfaces();
        bout.writeInt(ifaces.length);
        for (int i = 0; i < ifaces.length; i++) {
            bout.writeUTF(ifaces[i].getName());
        }
        bout.setBlockDataMode(true);
        annotateProxyClass(cl);
        bout.setBlockDataMode(false);
        bout.writeByte(TC_ENDBLOCKDATA);
        writeClassDesc(desc.getSuperDesc(), false);
    }
    
    private void writeNonProxyDesc(ObjectStreamClass desc, boolean unshared) throws IOException {
        bout.writeByte(TC_CLASSDESC);
        handles.assign(unshared ? null : desc);
        if (protocol == PROTOCOL_VERSION_1) {
            desc.writeNonProxy(this);
        } else {
            writeClassDescriptor(desc);
        }
        Class cl = desc.forClass();
        bout.setBlockDataMode(true);
        annotateClass(cl);
        bout.setBlockDataMode(false);
        bout.writeByte(TC_ENDBLOCKDATA);
        writeClassDesc(desc.getSuperDesc(), false);
    }
    
    private void writeString(String str, boolean unshared) throws IOException {
        handles.assign(unshared ? null : str);
        long utflen = bout.getUTFLength(str);
        if (utflen <= 65535) {
            bout.writeByte(TC_STRING);
            bout.writeUTF(str, utflen);
        } else {
            bout.writeByte(TC_LONGSTRING);
            bout.writeLongUTF(str, utflen);
        }
    }
    
    private void writeArray(Object array, ObjectStreamClass desc, boolean unshared) throws IOException {
        bout.writeByte(TC_ARRAY);
        writeClassDesc(desc, false);
        handles.assign(unshared ? null : array);
        Class ccl = desc.forClass().getComponentType();
        if (ccl.isPrimitive()) {
            if (ccl == Integer.TYPE) {
                int[] ia = (int[])(int[])array;
                bout.writeInt(ia.length);
                bout.writeInts(ia, 0, ia.length);
            } else if (ccl == Byte.TYPE) {
                byte[] ba = (byte[])(byte[])array;
                bout.writeInt(ba.length);
                bout.write(ba, 0, ba.length, true);
            } else if (ccl == Long.TYPE) {
                long[] ja = (long[])(long[])array;
                bout.writeInt(ja.length);
                bout.writeLongs(ja, 0, ja.length);
            } else if (ccl == Float.TYPE) {
                float[] fa = (float[])(float[])array;
                bout.writeInt(fa.length);
                bout.writeFloats(fa, 0, fa.length);
            } else if (ccl == Double.TYPE) {
                double[] da = (double[])(double[])array;
                bout.writeInt(da.length);
                bout.writeDoubles(da, 0, da.length);
            } else if (ccl == Short.TYPE) {
                short[] sa = (short[])(short[])array;
                bout.writeInt(sa.length);
                bout.writeShorts(sa, 0, sa.length);
            } else if (ccl == Character.TYPE) {
                char[] ca = (char[])(char[])array;
                bout.writeInt(ca.length);
                bout.writeChars(ca, 0, ca.length);
            } else if (ccl == Boolean.TYPE) {
                boolean[] za = (boolean[])(boolean[])array;
                bout.writeInt(za.length);
                bout.writeBooleans(za, 0, za.length);
            } else {
                throw new InternalError();
            }
        } else {
            Object[] objs = (Object[])(Object[])array;
            int len = objs.length;
            bout.writeInt(len);
            for (int i = 0; i < len; i++) {
                writeObject0(objs[i], false);
            }
        }
    }
    
    private void writeEnum(Enum en, ObjectStreamClass desc, boolean unshared) throws IOException {
        bout.writeByte(TC_ENUM);
        ObjectStreamClass sdesc = desc.getSuperDesc();
        writeClassDesc((sdesc.forClass() == Enum.class) ? desc : sdesc, false);
        handles.assign(unshared ? null : en);
        writeString(en.name(), false);
    }
    
    private void writeOrdinaryObject(Object obj, ObjectStreamClass desc, boolean unshared) throws IOException {
        desc.checkSerialize();
        bout.writeByte(TC_OBJECT);
        writeClassDesc(desc, false);
        handles.assign(unshared ? null : obj);
        if (desc.isExternalizable() && !desc.isProxy()) {
            writeExternalData((Externalizable)(Externalizable)obj);
        } else {
            writeSerialData(obj, desc);
        }
    }
    
    private void writeExternalData(Externalizable obj) throws IOException {
        Object oldObj = curObj;
        ObjectStreamClass oldDesc = curDesc;
        ObjectOutputStream$PutFieldImpl oldPut = curPut;
        curObj = obj;
        curDesc = null;
        curPut = null;
        if (protocol == PROTOCOL_VERSION_1) {
            obj.writeExternal(this);
        } else {
            bout.setBlockDataMode(true);
            obj.writeExternal(this);
            bout.setBlockDataMode(false);
            bout.writeByte(TC_ENDBLOCKDATA);
        }
        curObj = oldObj;
        curDesc = oldDesc;
        curPut = oldPut;
    }
    
    private void writeSerialData(Object obj, ObjectStreamClass desc) throws IOException {
        ObjectStreamClass$ClassDataSlot[] slots = desc.getClassDataLayout();
        for (int i = 0; i < slots.length; i++) {
            ObjectStreamClass slotDesc = slots[i].desc;
            if (slotDesc.hasWriteObjectMethod()) {
                Object oldObj = curObj;
                ObjectStreamClass oldDesc = curDesc;
                ObjectOutputStream$PutFieldImpl oldPut = curPut;
                curObj = obj;
                curDesc = slotDesc;
                curPut = null;
                bout.setBlockDataMode(true);
                slotDesc.invokeWriteObject(obj, this);
                bout.setBlockDataMode(false);
                bout.writeByte(TC_ENDBLOCKDATA);
                curObj = oldObj;
                curDesc = oldDesc;
                curPut = oldPut;
            } else {
                defaultWriteFields(obj, slotDesc);
            }
        }
    }
    
    private void defaultWriteFields(Object obj, ObjectStreamClass desc) throws IOException {
        desc.checkDefaultSerialize();
        int primDataSize = desc.getPrimDataSize();
        if (primVals == null || primVals.length < primDataSize) {
            primVals = new byte[primDataSize];
        }
        desc.getPrimFieldValues(obj, primVals);
        bout.write(primVals, 0, primDataSize, false);
        ObjectStreamField[] fields = desc.getFields(false);
        Object[] objVals = new Object[desc.getNumObjFields()];
        int numPrimFields = fields.length - objVals.length;
        desc.getObjFieldValues(obj, objVals);
        for (int i = 0; i < objVals.length; i++) {
            writeObject0(objVals[i], fields[numPrimFields + i].isUnshared());
        }
    }
    
    private void writeFatalException(IOException ex) throws IOException {
        clear();
        boolean oldMode = bout.setBlockDataMode(false);
        try {
            bout.writeByte(TC_EXCEPTION);
            writeObject0(ex, false);
            clear();
        } finally {
            bout.setBlockDataMode(oldMode);
        }
    }
    
    private static native void floatsToBytes(float[] src, int srcpos, byte[] dst, int dstpos, int nfloats);
    
    private static native void doublesToBytes(double[] src, int srcpos, byte[] dst, int dstpos, int ndoubles);
    {
    }
    {
    }
    {
    }
    {
    }
}
