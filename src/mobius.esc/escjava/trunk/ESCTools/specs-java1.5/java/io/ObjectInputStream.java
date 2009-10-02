package java.io;

import java.io.ObjectStreamClass.WeakClassKey;
import java.lang.reflect.Array;
import java.lang.reflect.Modifier;
import java.lang.reflect.Proxy;
import java.security.AccessController;
import java.util.HashMap;

public class ObjectInputStream extends InputStream implements ObjectInput, ObjectStreamConstants {
    
    /*synthetic*/ static void access$700(byte[] x0, int x1, double[] x2, int x3, int x4) {
        bytesToDoubles(x0, x1, x2, x3, x4);
    }
    
    /*synthetic*/ static void access$600(byte[] x0, int x1, float[] x2, int x3, int x4) {
        bytesToFloats(x0, x1, x2, x3, x4);
    }
    
    /*synthetic*/ static void access$500(ObjectInputStream x0) throws StreamCorruptedException {
        x0.handleReset();
    }
    
    /*synthetic*/ static boolean access$400(ObjectInputStream x0) {
        return x0.defaultDataEnd;
    }
    
    /*synthetic*/ static Object access$300(ObjectInputStream x0, boolean x1) throws IOException {
        return x0.readObject0(x1);
    }
    
    /*synthetic*/ static ObjectInputStream$BlockDataInputStream access$200(ObjectInputStream x0) {
        return x0.bin;
    }
    
    /*synthetic*/ static ObjectInputStream$HandleTable access$100(ObjectInputStream x0) {
        return x0.handles;
    }
    
    /*synthetic*/ static int access$002(ObjectInputStream x0, int x1) {
        return x0.passHandle = x1;
    }
    
    /*synthetic*/ static int access$000(ObjectInputStream x0) {
        return x0.passHandle;
    }
    private static final int NULL_HANDLE = -1;
    private static final Object unsharedMarker = new Object();
    private static final HashMap primClasses = new HashMap(8, 1.0F);
    static {
        primClasses.put("boolean", Boolean.TYPE);
        primClasses.put("byte", Byte.TYPE);
        primClasses.put("char", Character.TYPE);
        primClasses.put("short", Short.TYPE);
        primClasses.put("int", Integer.TYPE);
        primClasses.put("long", Long.TYPE);
        primClasses.put("float", Float.TYPE);
        primClasses.put("double", Double.TYPE);
        primClasses.put("void", Void.TYPE);
    }
    {
    }
    private final ObjectInputStream$BlockDataInputStream bin;
    private final ObjectInputStream$ValidationList vlist;
    private int depth;
    private boolean closed;
    private final ObjectInputStream$HandleTable handles;
    private int passHandle = NULL_HANDLE;
    private boolean defaultDataEnd = false;
    private byte[] primVals;
    private final boolean enableOverride;
    private boolean enableResolve;
    private ObjectInputStream$CallbackContext curContext;
    
    public ObjectInputStream(InputStream in) throws IOException {
        
        verifySubclass();
        bin = new ObjectInputStream$BlockDataInputStream(this, in);
        handles = new ObjectInputStream$HandleTable(10);
        vlist = new ObjectInputStream$ValidationList();
        enableOverride = false;
        readStreamHeader();
        bin.setBlockDataMode(true);
    }
    
    protected ObjectInputStream() throws IOException, SecurityException {
        
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(SUBCLASS_IMPLEMENTATION_PERMISSION);
        }
        bin = null;
        handles = null;
        vlist = null;
        enableOverride = true;
    }
    
    public final Object readObject() throws IOException, ClassNotFoundException {
        if (enableOverride) {
            return readObjectOverride();
        }
        int outerHandle = passHandle;
        try {
            Object obj = readObject0(false);
            handles.markDependency(outerHandle, passHandle);
            ClassNotFoundException ex = handles.lookupException(passHandle);
            if (ex != null) {
                throw ex;
            }
            if (depth == 0) {
                vlist.doCallbacks();
            }
            return obj;
        } finally {
            passHandle = outerHandle;
            if (closed && depth == 0) {
                clear();
            }
        }
    }
    
    protected Object readObjectOverride() throws IOException, ClassNotFoundException {
        return null;
    }
    
    public Object readUnshared() throws IOException, ClassNotFoundException {
        int outerHandle = passHandle;
        try {
            Object obj = readObject0(true);
            handles.markDependency(outerHandle, passHandle);
            ClassNotFoundException ex = handles.lookupException(passHandle);
            if (ex != null) {
                throw ex;
            }
            if (depth == 0) {
                vlist.doCallbacks();
            }
            return obj;
        } finally {
            passHandle = outerHandle;
            if (closed && depth == 0) {
                clear();
            }
        }
    }
    
    public void defaultReadObject() throws IOException, ClassNotFoundException {
        if (curContext == null) {
            throw new NotActiveException("not in call to readObject");
        }
        Object curObj = curContext.getObj();
        ObjectStreamClass curDesc = curContext.getDesc();
        bin.setBlockDataMode(false);
        defaultReadFields(curObj, curDesc);
        bin.setBlockDataMode(true);
        if (!curDesc.hasWriteObjectData()) {
            defaultDataEnd = true;
        }
        ClassNotFoundException ex = handles.lookupException(passHandle);
        if (ex != null) {
            throw ex;
        }
    }
    
    public ObjectInputStream$GetField readFields() throws IOException, ClassNotFoundException {
        if (curContext == null) {
            throw new NotActiveException("not in call to readObject");
        }
        Object curObj = curContext.getObj();
        ObjectStreamClass curDesc = curContext.getDesc();
        bin.setBlockDataMode(false);
        ObjectInputStream$GetFieldImpl getField = new ObjectInputStream$GetFieldImpl(this, curDesc);
        getField.readFields();
        bin.setBlockDataMode(true);
        if (!curDesc.hasWriteObjectData()) {
            defaultDataEnd = true;
        }
        return getField;
    }
    
    public void registerValidation(ObjectInputValidation obj, int prio) throws NotActiveException, InvalidObjectException {
        if (depth == 0) {
            throw new NotActiveException("stream inactive");
        }
        vlist.register(obj, prio);
    }
    
    protected Class resolveClass(ObjectStreamClass desc) throws IOException, ClassNotFoundException {
        String name = desc.getName();
        try {
            return Class.forName(name, false, latestUserDefinedLoader());
        } catch (ClassNotFoundException ex) {
            Class cl = (Class)(Class)primClasses.get(name);
            if (cl != null) {
                return cl;
            } else {
                throw ex;
            }
        }
    }
    
    protected Class resolveProxyClass(String[] interfaces) throws IOException, ClassNotFoundException {
        ClassLoader latestLoader = latestUserDefinedLoader();
        ClassLoader nonPublicLoader = null;
        boolean hasNonPublicInterface = false;
        Class[] classObjs = new Class[interfaces.length];
        for (int i = 0; i < interfaces.length; i++) {
            Class cl = Class.forName(interfaces[i], false, latestLoader);
            if ((cl.getModifiers() & Modifier.PUBLIC) == 0) {
                if (hasNonPublicInterface) {
                    if (nonPublicLoader != cl.getClassLoader()) {
                        throw new IllegalAccessError("conflicting non-public interface class loaders");
                    }
                } else {
                    nonPublicLoader = cl.getClassLoader();
                    hasNonPublicInterface = true;
                }
            }
            classObjs[i] = cl;
        }
        try {
            return Proxy.getProxyClass(hasNonPublicInterface ? nonPublicLoader : latestLoader, classObjs);
        } catch (IllegalArgumentException e) {
            throw new ClassNotFoundException(null, e);
        }
    }
    
    protected Object resolveObject(Object obj) throws IOException {
        return obj;
    }
    
    protected boolean enableResolveObject(boolean enable) throws SecurityException {
        if (enable == enableResolve) {
            return enable;
        }
        if (enable) {
            SecurityManager sm = System.getSecurityManager();
            if (sm != null) {
                sm.checkPermission(SUBSTITUTION_PERMISSION);
            }
        }
        enableResolve = enable;
        return !enableResolve;
    }
    
    protected void readStreamHeader() throws IOException, StreamCorruptedException {
        if (bin.readShort() != STREAM_MAGIC || bin.readShort() != STREAM_VERSION) {
            throw new StreamCorruptedException("invalid stream header");
        }
    }
    
    protected ObjectStreamClass readClassDescriptor() throws IOException, ClassNotFoundException {
        ObjectStreamClass desc = new ObjectStreamClass();
        desc.readNonProxy(this);
        return desc;
    }
    
    public int read() throws IOException {
        return bin.read();
    }
    
    public int read(byte[] buf, int off, int len) throws IOException {
        if (buf == null) {
            throw new NullPointerException();
        }
        int endoff = off + len;
        if (off < 0 || len < 0 || endoff > buf.length || endoff < 0) {
            throw new IndexOutOfBoundsException();
        }
        return bin.read(buf, off, len, false);
    }
    
    public int available() throws IOException {
        return bin.available();
    }
    
    public void close() throws IOException {
        closed = true;
        if (depth == 0) {
            clear();
        }
        bin.close();
    }
    
    public boolean readBoolean() throws IOException {
        return bin.readBoolean();
    }
    
    public byte readByte() throws IOException {
        return bin.readByte();
    }
    
    public int readUnsignedByte() throws IOException {
        return bin.readUnsignedByte();
    }
    
    public char readChar() throws IOException {
        return bin.readChar();
    }
    
    public short readShort() throws IOException {
        return bin.readShort();
    }
    
    public int readUnsignedShort() throws IOException {
        return bin.readUnsignedShort();
    }
    
    public int readInt() throws IOException {
        return bin.readInt();
    }
    
    public long readLong() throws IOException {
        return bin.readLong();
    }
    
    public float readFloat() throws IOException {
        return bin.readFloat();
    }
    
    public double readDouble() throws IOException {
        return bin.readDouble();
    }
    
    public void readFully(byte[] buf) throws IOException {
        bin.readFully(buf, 0, buf.length, false);
    }
    
    public void readFully(byte[] buf, int off, int len) throws IOException {
        int endoff = off + len;
        if (off < 0 || len < 0 || endoff > buf.length || endoff < 0) {
            throw new IndexOutOfBoundsException();
        }
        bin.readFully(buf, off, len, false);
    }
    
    public int skipBytes(int len) throws IOException {
        return bin.skipBytes(len);
    }
    
    
    public String readLine() throws IOException {
        return bin.readLine();
    }
    
    public String readUTF() throws IOException {
        return bin.readUTF();
    }
    {
    }
    
    private void verifySubclass() {
        Class cl = getClass();
        ObjectStreamClass.processQueue(ObjectInputStream$Caches.subclassAuditsQueue, ObjectInputStream$Caches.subclassAudits);
        ObjectStreamClass$WeakClassKey key = new ObjectStreamClass$WeakClassKey(cl, ObjectInputStream$Caches.subclassAuditsQueue);
        Boolean result = (Boolean)ObjectInputStream$Caches.subclassAudits.get(key);
        if (result == null) {
            result = Boolean.valueOf(auditSubclass(cl));
            ObjectInputStream$Caches.subclassAudits.putIfAbsent(key, result);
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
        Boolean result = (Boolean)(Boolean)AccessController.doPrivileged(new ObjectInputStream$1(subcl));
        return result.booleanValue();
    }
    
    private void clear() {
        handles.clear();
        vlist.clear();
    }
    
    private Object readObject0(boolean unshared) throws IOException {
        boolean oldMode = bin.getBlockDataMode();
        if (oldMode) {
            int remain = bin.currentBlockRemaining();
            if (remain > 0) {
                throw new OptionalDataException(remain);
            } else if (defaultDataEnd) {
                throw new OptionalDataException(true);
            }
            bin.setBlockDataMode(false);
        }
        byte tc;
        while ((tc = bin.peekByte()) == TC_RESET) {
            bin.readByte();
            handleReset();
        }
        depth++;
        try {
            switch (tc) {
            case TC_NULL: 
                return readNull();
            
            case TC_REFERENCE: 
                return readHandle(unshared);
            
            case TC_CLASS: 
                return readClass(unshared);
            
            case TC_CLASSDESC: 
            
            case TC_PROXYCLASSDESC: 
                return readClassDesc(unshared);
            
            case TC_STRING: 
            
            case TC_LONGSTRING: 
                return checkResolve(readString(unshared));
            
            case TC_ARRAY: 
                return checkResolve(readArray(unshared));
            
            case TC_ENUM: 
                return checkResolve(readEnum(unshared));
            
            case TC_OBJECT: 
                return checkResolve(readOrdinaryObject(unshared));
            
            case TC_EXCEPTION: 
                IOException ex = readFatalException();
                throw new WriteAbortedException("writing aborted", ex);
            
            case TC_BLOCKDATA: 
            
            case TC_BLOCKDATALONG: 
                if (oldMode) {
                    bin.setBlockDataMode(true);
                    bin.peek();
                    throw new OptionalDataException(bin.currentBlockRemaining());
                } else {
                    throw new StreamCorruptedException("unexpected block data");
                }
            
            case TC_ENDBLOCKDATA: 
                if (oldMode) {
                    throw new OptionalDataException(true);
                } else {
                    throw new StreamCorruptedException("unexpected end of block data");
                }
            
            default: 
                throw new StreamCorruptedException();
            
            }
        } finally {
            depth--;
            bin.setBlockDataMode(oldMode);
        }
    }
    
    private Object checkResolve(Object obj) throws IOException {
        if (!enableResolve || handles.lookupException(passHandle) != null) {
            return obj;
        }
        Object r = resolveObject(obj);
        if (r != obj) {
            handles.setObject(passHandle, r);
        }
        return r;
    }
    
    String readTypeString() throws IOException {
        int oldHandle = passHandle;
        try {
            switch (bin.peekByte()) {
            case TC_NULL: 
                return (String)(String)readNull();
            
            case TC_REFERENCE: 
                return (String)(String)readHandle(false);
            
            case TC_STRING: 
            
            case TC_LONGSTRING: 
                return readString(false);
            
            default: 
                throw new StreamCorruptedException();
            
            }
        } finally {
            passHandle = oldHandle;
        }
    }
    
    private Object readNull() throws IOException {
        if (bin.readByte() != TC_NULL) {
            throw new StreamCorruptedException();
        }
        passHandle = NULL_HANDLE;
        return null;
    }
    
    private Object readHandle(boolean unshared) throws IOException {
        if (bin.readByte() != TC_REFERENCE) {
            throw new StreamCorruptedException();
        }
        passHandle = bin.readInt() - baseWireHandle;
        if (passHandle < 0 || passHandle >= handles.size()) {
            throw new StreamCorruptedException("illegal handle value");
        }
        if (unshared) {
            throw new InvalidObjectException("cannot read back reference as unshared");
        }
        Object obj = handles.lookupObject(passHandle);
        if (obj == unsharedMarker) {
            throw new InvalidObjectException("cannot read back reference to unshared object");
        }
        return obj;
    }
    
    private Class readClass(boolean unshared) throws IOException {
        if (bin.readByte() != TC_CLASS) {
            throw new StreamCorruptedException();
        }
        ObjectStreamClass desc = readClassDesc(false);
        Class cl = desc.forClass();
        passHandle = handles.assign(unshared ? unsharedMarker : cl);
        ClassNotFoundException resolveEx = desc.getResolveException();
        if (resolveEx != null) {
            handles.markException(passHandle, resolveEx);
        }
        handles.finish(passHandle);
        return cl;
    }
    
    private ObjectStreamClass readClassDesc(boolean unshared) throws IOException {
        switch (bin.peekByte()) {
        case TC_NULL: 
            return (ObjectStreamClass)(ObjectStreamClass)readNull();
        
        case TC_REFERENCE: 
            return (ObjectStreamClass)(ObjectStreamClass)readHandle(unshared);
        
        case TC_PROXYCLASSDESC: 
            return readProxyDesc(unshared);
        
        case TC_CLASSDESC: 
            return readNonProxyDesc(unshared);
        
        default: 
            throw new StreamCorruptedException();
        
        }
    }
    
    private ObjectStreamClass readProxyDesc(boolean unshared) throws IOException {
        if (bin.readByte() != TC_PROXYCLASSDESC) {
            throw new StreamCorruptedException();
        }
        ObjectStreamClass desc = new ObjectStreamClass();
        int descHandle = handles.assign(unshared ? unsharedMarker : desc);
        passHandle = NULL_HANDLE;
        int numIfaces = bin.readInt();
        String[] ifaces = new String[numIfaces];
        for (int i = 0; i < numIfaces; i++) {
            ifaces[i] = bin.readUTF();
        }
        Class cl = null;
        ClassNotFoundException resolveEx = null;
        bin.setBlockDataMode(true);
        try {
            if ((cl = resolveProxyClass(ifaces)) == null) {
                throw new ClassNotFoundException("null class");
            }
        } catch (ClassNotFoundException ex) {
            resolveEx = ex;
        }
        skipCustomData();
        desc.initProxy(cl, resolveEx, readClassDesc(false));
        handles.finish(descHandle);
        passHandle = descHandle;
        return desc;
    }
    
    private ObjectStreamClass readNonProxyDesc(boolean unshared) throws IOException {
        if (bin.readByte() != TC_CLASSDESC) {
            throw new StreamCorruptedException();
        }
        ObjectStreamClass desc = new ObjectStreamClass();
        int descHandle = handles.assign(unshared ? unsharedMarker : desc);
        passHandle = NULL_HANDLE;
        ObjectStreamClass readDesc = null;
        try {
            readDesc = readClassDescriptor();
        } catch (ClassNotFoundException ex) {
            throw (IOException)(IOException)new InvalidClassException("failed to read class descriptor").initCause(ex);
        }
        Class cl = null;
        ClassNotFoundException resolveEx = null;
        bin.setBlockDataMode(true);
        try {
            if ((cl = resolveClass(readDesc)) == null) {
                throw new ClassNotFoundException("null class");
            }
        } catch (ClassNotFoundException ex) {
            resolveEx = ex;
        }
        skipCustomData();
        desc.initNonProxy(readDesc, cl, resolveEx, readClassDesc(false));
        handles.finish(descHandle);
        passHandle = descHandle;
        return desc;
    }
    
    private String readString(boolean unshared) throws IOException {
        String str;
        switch (bin.readByte()) {
        case TC_STRING: 
            str = bin.readUTF();
            break;
        
        case TC_LONGSTRING: 
            str = bin.readLongUTF();
            break;
        
        default: 
            throw new StreamCorruptedException();
        
        }
        passHandle = handles.assign(unshared ? unsharedMarker : str);
        handles.finish(passHandle);
        return str;
    }
    
    private Object readArray(boolean unshared) throws IOException {
        if (bin.readByte() != TC_ARRAY) {
            throw new StreamCorruptedException();
        }
        ObjectStreamClass desc = readClassDesc(false);
        int len = bin.readInt();
        Object array = null;
        Class cl;
        Class ccl = null;
        if ((cl = desc.forClass()) != null) {
            ccl = cl.getComponentType();
            array = Array.newInstance(ccl, len);
        }
        int arrayHandle = handles.assign(unshared ? unsharedMarker : array);
        ClassNotFoundException resolveEx = desc.getResolveException();
        if (resolveEx != null) {
            handles.markException(arrayHandle, resolveEx);
        }
        if (ccl == null) {
            for (int i = 0; i < len; i++) {
                readObject0(false);
            }
        } else if (ccl.isPrimitive()) {
            if (ccl == Integer.TYPE) {
                bin.readInts((int[])(int[])array, 0, len);
            } else if (ccl == Byte.TYPE) {
                bin.readFully((byte[])(byte[])array, 0, len, true);
            } else if (ccl == Long.TYPE) {
                bin.readLongs((long[])(long[])array, 0, len);
            } else if (ccl == Float.TYPE) {
                bin.readFloats((float[])(float[])array, 0, len);
            } else if (ccl == Double.TYPE) {
                bin.readDoubles((double[])(double[])array, 0, len);
            } else if (ccl == Short.TYPE) {
                bin.readShorts((short[])(short[])array, 0, len);
            } else if (ccl == Character.TYPE) {
                bin.readChars((char[])(char[])array, 0, len);
            } else if (ccl == Boolean.TYPE) {
                bin.readBooleans((boolean[])(boolean[])array, 0, len);
            } else {
                throw new InternalError();
            }
        } else {
            Object[] oa = (Object[])(Object[])array;
            for (int i = 0; i < len; i++) {
                oa[i] = readObject0(false);
                handles.markDependency(arrayHandle, passHandle);
            }
        }
        handles.finish(arrayHandle);
        passHandle = arrayHandle;
        return array;
    }
    
    private Enum readEnum(boolean unshared) throws IOException {
        if (bin.readByte() != TC_ENUM) {
            throw new StreamCorruptedException();
        }
        ObjectStreamClass desc = readClassDesc(false);
        if (!desc.isEnum()) {
            throw new InvalidClassException("non-enum class: " + desc);
        }
        int enumHandle = handles.assign(unshared ? unsharedMarker : null);
        ClassNotFoundException resolveEx = desc.getResolveException();
        if (resolveEx != null) {
            handles.markException(enumHandle, resolveEx);
        }
        String name = readString(false);
        Enum en = null;
        Class cl = desc.forClass();
        if (cl != null) {
            try {
                en = Enum.valueOf(cl, name);
            } catch (IllegalArgumentException ex) {
                throw (IOException)(IOException)new InvalidObjectException("enum constant " + name + " does not exist in " + cl).initCause(ex);
            }
            if (!unshared) {
                handles.setObject(enumHandle, en);
            }
        }
        handles.finish(enumHandle);
        passHandle = enumHandle;
        return en;
    }
    
    private Object readOrdinaryObject(boolean unshared) throws IOException {
        if (bin.readByte() != TC_OBJECT) {
            throw new StreamCorruptedException();
        }
        ObjectStreamClass desc = readClassDesc(false);
        desc.checkDeserialize();
        Object obj;
        try {
            obj = desc.isInstantiable() ? desc.newInstance() : null;
        } catch (Exception ex) {
            throw new InvalidClassException(desc.forClass().getName(), "unable to create instance");
        }
        passHandle = handles.assign(unshared ? unsharedMarker : obj);
        ClassNotFoundException resolveEx = desc.getResolveException();
        if (resolveEx != null) {
            handles.markException(passHandle, resolveEx);
        }
        if (desc.isExternalizable()) {
            readExternalData((Externalizable)(Externalizable)obj, desc);
        } else {
            readSerialData(obj, desc);
        }
        handles.finish(passHandle);
        if (obj != null && handles.lookupException(passHandle) == null && desc.hasReadResolveMethod()) {
            Object r = desc.invokeReadResolve(obj);
            if (r != obj) {
                handles.setObject(passHandle, obj = r);
            }
        }
        return obj;
    }
    
    private void readExternalData(Externalizable obj, ObjectStreamClass desc) throws IOException {
        ObjectInputStream$CallbackContext oldContext = curContext;
        curContext = null;
        boolean blocked = desc.hasBlockExternalData();
        if (blocked) {
            bin.setBlockDataMode(true);
        }
        if (obj != null) {
            try {
                obj.readExternal(this);
            } catch (ClassNotFoundException ex) {
                handles.markException(passHandle, ex);
            }
        }
        if (blocked) {
            skipCustomData();
        }
        curContext = oldContext;
    }
    
    private void readSerialData(Object obj, ObjectStreamClass desc) throws IOException {
        ObjectStreamClass$ClassDataSlot[] slots = desc.getClassDataLayout();
        for (int i = 0; i < slots.length; i++) {
            ObjectStreamClass slotDesc = slots[i].desc;
            if (slots[i].hasData) {
                if (obj != null && slotDesc.hasReadObjectMethod() && handles.lookupException(passHandle) == null) {
                    ObjectInputStream$CallbackContext oldContext = curContext;
                    curContext = new ObjectInputStream$CallbackContext(obj, slotDesc);
                    bin.setBlockDataMode(true);
                    try {
                        slotDesc.invokeReadObject(obj, this);
                    } catch (ClassNotFoundException ex) {
                        handles.markException(passHandle, ex);
                    } finally {
                        curContext.setUsed();
                    }
                    curContext = oldContext;
                    defaultDataEnd = false;
                } else {
                    defaultReadFields(obj, slotDesc);
                }
                if (slotDesc.hasWriteObjectData()) {
                    skipCustomData();
                } else {
                    bin.setBlockDataMode(false);
                }
            } else {
                if (obj != null && slotDesc.hasReadObjectNoDataMethod() && handles.lookupException(passHandle) == null) {
                    slotDesc.invokeReadObjectNoData(obj);
                }
            }
        }
    }
    
    private void skipCustomData() throws IOException {
        int oldHandle = passHandle;
        for (; ; ) {
            if (bin.getBlockDataMode()) {
                bin.skipBlockData();
                bin.setBlockDataMode(false);
            }
            switch (bin.peekByte()) {
            case TC_BLOCKDATA: 
            
            case TC_BLOCKDATALONG: 
                bin.setBlockDataMode(true);
                break;
            
            case TC_ENDBLOCKDATA: 
                bin.readByte();
                passHandle = oldHandle;
                return;
            
            default: 
                readObject0(false);
                break;
            
            }
        }
    }
    
    private void defaultReadFields(Object obj, ObjectStreamClass desc) throws IOException {
        Class cl = desc.forClass();
        if (cl != null && obj != null && !cl.isInstance(obj)) {
            throw new ClassCastException();
        }
        int primDataSize = desc.getPrimDataSize();
        if (primVals == null || primVals.length < primDataSize) {
            primVals = new byte[primDataSize];
        }
        bin.readFully(primVals, 0, primDataSize, false);
        if (obj != null) {
            desc.setPrimFieldValues(obj, primVals);
        }
        int objHandle = passHandle;
        ObjectStreamField[] fields = desc.getFields(false);
        Object[] objVals = new Object[desc.getNumObjFields()];
        int numPrimFields = fields.length - objVals.length;
        for (int i = 0; i < objVals.length; i++) {
            ObjectStreamField f = fields[numPrimFields + i];
            objVals[i] = readObject0(f.isUnshared());
            if (f.getField() != null) {
                handles.markDependency(objHandle, passHandle);
            }
        }
        if (obj != null) {
            desc.setObjFieldValues(obj, objVals);
        }
        passHandle = objHandle;
    }
    
    private IOException readFatalException() throws IOException {
        if (bin.readByte() != TC_EXCEPTION) {
            throw new StreamCorruptedException();
        }
        clear();
        return (IOException)(IOException)readObject0(false);
    }
    
    private void handleReset() throws StreamCorruptedException {
        if (depth > 0) {
            throw new StreamCorruptedException("unexpected reset");
        }
        clear();
    }
    
    private static native void bytesToFloats(byte[] src, int srcpos, float[] dst, int dstpos, int nfloats);
    
    private static native void bytesToDoubles(byte[] src, int srcpos, double[] dst, int dstpos, int ndoubles);
    
    private static native ClassLoader latestUserDefinedLoader();
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
}
