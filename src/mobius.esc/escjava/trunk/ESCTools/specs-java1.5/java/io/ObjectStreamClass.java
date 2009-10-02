package java.io;

import java.lang.ref.Reference;
import java.lang.ref.ReferenceQueue;
import java.lang.ref.SoftReference;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Proxy;
import java.security.AccessController;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.ConcurrentMap;
import sun.reflect.ReflectionFactory;

public class ObjectStreamClass implements Serializable {
    
    /*synthetic*/ static String access$2400(Class[] x0, Class x1) {
        return getMethodSignature(x0, x1);
    }
    
    /*synthetic*/ static Method access$2302(ObjectStreamClass x0, Method x1) {
        return x0.readResolveMethod = x1;
    }
    
    /*synthetic*/ static Method access$2200(Class x0, String x1, Class[] x2, Class x3) {
        return getInheritableMethod(x0, x1, x2, x3);
    }
    
    /*synthetic*/ static Method access$2102(ObjectStreamClass x0, Method x1) {
        return x0.writeReplaceMethod = x1;
    }
    
    /*synthetic*/ static boolean access$2002(ObjectStreamClass x0, boolean x1) {
        return x0.hasWriteObjectData = x1;
    }
    
    /*synthetic*/ static Method access$1902(ObjectStreamClass x0, Method x1) {
        return x0.readObjectNoDataMethod = x1;
    }
    
    /*synthetic*/ static Method access$1802(ObjectStreamClass x0, Method x1) {
        return x0.readObjectMethod = x1;
    }
    
    /*synthetic*/ static Method access$1700(Class x0, String x1, Class[] x2, Class x3) {
        return getPrivateMethod(x0, x1, x2, x3);
    }
    
    /*synthetic*/ static Method access$1602(ObjectStreamClass x0, Method x1) {
        return x0.writeObjectMethod = x1;
    }
    
    /*synthetic*/ static Method access$1600(ObjectStreamClass x0) {
        return x0.writeObjectMethod;
    }
    
    /*synthetic*/ static Constructor access$1500(Class x0) {
        return getSerializableConstructor(x0);
    }
    
    /*synthetic*/ static Constructor access$1400(Class x0) {
        return getExternalizableConstructor(x0);
    }
    
    /*synthetic*/ static Constructor access$1302(ObjectStreamClass x0, Constructor x1) {
        return x0.cons = x1;
    }
    
    /*synthetic*/ static boolean access$1200(ObjectStreamClass x0) {
        return x0.externalizable;
    }
    
    /*synthetic*/ static InvalidClassException access$1102(ObjectStreamClass x0, InvalidClassException x1) {
        return x0.deserializeEx = x1;
    }
    
    /*synthetic*/ static InvalidClassException access$1002(ObjectStreamClass x0, InvalidClassException x1) {
        return x0.serializeEx = x1;
    }
    
    /*synthetic*/ static void access$900(ObjectStreamClass x0) throws InvalidClassException {
        x0.computeFieldOffsets();
    }
    
    /*synthetic*/ static ObjectStreamField[] access$800(Class x0) throws InvalidClassException {
        return getSerialFields(x0);
    }
    
    /*synthetic*/ static Long access$700(Class x0) {
        return getDeclaredSUID(x0);
    }
    
    /*synthetic*/ static ObjectStreamField[] access$602(ObjectStreamClass x0, ObjectStreamField[] x1) {
        return x0.fields = x1;
    }
    
    /*synthetic*/ static Long access$502(ObjectStreamClass x0, Long x1) {
        return x0.suid = x1;
    }
    
    /*synthetic*/ static boolean access$400(ObjectStreamClass x0) {
        return x0.isEnum;
    }
    
    /*synthetic*/ static long access$100(Class x0) {
        return computeDefaultSUID(x0);
    }
    
    /*synthetic*/ static Class access$000(ObjectStreamClass x0) {
        return x0.cl;
    }
    public static final ObjectStreamField[] NO_FIELDS = new ObjectStreamField[0];
    private static final long serialVersionUID = -6120832682080437368L;
    private static final ObjectStreamField[] serialPersistentFields = NO_FIELDS;
    private static final ReflectionFactory reflFactory = (ReflectionFactory)(ReflectionFactory)AccessController.doPrivileged(new ReflectionFactory$GetReflectionFactoryAction());
    {
    }
    private Class cl;
    private String name;
    private volatile Long suid;
    private boolean isProxy;
    private boolean isEnum;
    private boolean serializable;
    private boolean externalizable;
    private boolean hasWriteObjectData;
    private boolean hasBlockExternalData = true;
    private ClassNotFoundException resolveEx;
    private InvalidClassException deserializeEx;
    private InvalidClassException serializeEx;
    private InvalidClassException defaultSerializeEx;
    private ObjectStreamField[] fields;
    private int primDataSize;
    private int numObjFields;
    private ObjectStreamClass$FieldReflector fieldRefl;
    private volatile ObjectStreamClass$ClassDataSlot[] dataLayout;
    private Constructor cons;
    private Method writeObjectMethod;
    private Method readObjectMethod;
    private Method readObjectNoDataMethod;
    private Method writeReplaceMethod;
    private Method readResolveMethod;
    private ObjectStreamClass localDesc;
    private ObjectStreamClass superDesc;
    
    private static native void initNative();
    static {
        initNative();
    }
    
    public static ObjectStreamClass lookup(Class cl) {
        return lookup(cl, false);
    }
    
    public String getName() {
        return name;
    }
    
    public long getSerialVersionUID() {
        if (suid == null) {
            suid = (Long)(Long)AccessController.doPrivileged(new ObjectStreamClass$1(this));
        }
        return suid.longValue();
    }
    
    public Class forClass() {
        return cl;
    }
    
    public ObjectStreamField[] getFields() {
        return getFields(true);
    }
    
    public ObjectStreamField getField(String name) {
        return getField(name, null);
    }
    
    public String toString() {
        return name + ": static final long serialVersionUID = " + getSerialVersionUID() + "L;";
    }
    
    static ObjectStreamClass lookup(Class cl, boolean all) {
        if (!(all || Serializable.class.isAssignableFrom(cl))) {
            return null;
        }
        processQueue(ObjectStreamClass$Caches.access$200(), ObjectStreamClass$Caches.localDescs);
        ObjectStreamClass$WeakClassKey key = new ObjectStreamClass$WeakClassKey(cl, ObjectStreamClass$Caches.access$200());
        Reference ref = (Reference)ObjectStreamClass$Caches.localDescs.get(key);
        Object entry = null;
        if (ref != null) {
            entry = ref.get();
        }
        ObjectStreamClass$EntryFuture future = null;
        if (entry == null) {
            ObjectStreamClass$EntryFuture newEntry = new ObjectStreamClass$EntryFuture(null);
            Reference newRef = new SoftReference(newEntry);
            do {
                if (ref != null) {
                    ObjectStreamClass$Caches.localDescs.remove(key, ref);
                }
                ref = (Reference)ObjectStreamClass$Caches.localDescs.putIfAbsent(key, newRef);
                if (ref != null) {
                    entry = ref.get();
                }
            }             while (ref != null && entry == null);
            if (entry == null) {
                future = newEntry;
            }
        }
        if (entry instanceof ObjectStreamClass) {
            return (ObjectStreamClass)(ObjectStreamClass)entry;
        }
        if (entry instanceof ObjectStreamClass$EntryFuture) {
            future = (ObjectStreamClass$EntryFuture)(ObjectStreamClass$EntryFuture)entry;
            if (future.getOwner() == Thread.currentThread()) {
                entry = null;
            } else {
                entry = future.get();
            }
        }
        if (entry == null) {
            try {
                entry = new ObjectStreamClass(cl);
            } catch (Throwable th) {
                entry = th;
            }
            if (future.set(entry)) {
                ObjectStreamClass$Caches.localDescs.put(key, new SoftReference(entry));
            } else {
                entry = future.get();
            }
        }
        if (entry instanceof ObjectStreamClass) {
            return (ObjectStreamClass)(ObjectStreamClass)entry;
        } else if (entry instanceof RuntimeException) {
            throw (RuntimeException)(RuntimeException)entry;
        } else if (entry instanceof Error) {
            throw (Error)(Error)entry;
        } else {
            throw new InternalError("unexpected entry: " + entry);
        }
    }
    {
    }
    
    private ObjectStreamClass(final Class cl) {
        
        this.cl = cl;
        name = cl.getName();
        isProxy = Proxy.isProxyClass(cl);
        isEnum = Enum.class.isAssignableFrom(cl);
        serializable = Serializable.class.isAssignableFrom(cl);
        externalizable = Externalizable.class.isAssignableFrom(cl);
        Class superCl = cl.getSuperclass();
        superDesc = (superCl != null) ? lookup(superCl, false) : null;
        localDesc = this;
        if (serializable) {
            AccessController.doPrivileged(new ObjectStreamClass$2(this, cl));
        } else {
            suid = new Long(0);
            fields = NO_FIELDS;
        }
        try {
            fieldRefl = getReflector(fields, this);
        } catch (InvalidClassException ex) {
            throw new InternalError();
        }
        if (deserializeEx == null) {
            if (isEnum) {
                deserializeEx = new InvalidClassException(name, "enum type");
            } else if (cons == null) {
                deserializeEx = new InvalidClassException(name, "no valid constructor");
            }
        }
        for (int i = 0; i < fields.length; i++) {
            if (fields[i].getField() == null) {
                defaultSerializeEx = new InvalidClassException(name, "unmatched serializable field(s) declared");
            }
        }
    }
    
    ObjectStreamClass() {
        
    }
    
    void initProxy(Class cl, ClassNotFoundException resolveEx, ObjectStreamClass superDesc) throws InvalidClassException {
        this.cl = cl;
        this.resolveEx = resolveEx;
        this.superDesc = superDesc;
        isProxy = true;
        serializable = true;
        suid = new Long(0);
        fields = NO_FIELDS;
        if (cl != null) {
            localDesc = lookup(cl, true);
            if (!localDesc.isProxy) {
                throw new InvalidClassException("cannot bind proxy descriptor to a non-proxy class");
            }
            name = localDesc.name;
            externalizable = localDesc.externalizable;
            cons = localDesc.cons;
            writeReplaceMethod = localDesc.writeReplaceMethod;
            readResolveMethod = localDesc.readResolveMethod;
            deserializeEx = localDesc.deserializeEx;
        }
        fieldRefl = getReflector(fields, localDesc);
    }
    
    void initNonProxy(ObjectStreamClass model, Class cl, ClassNotFoundException resolveEx, ObjectStreamClass superDesc) throws InvalidClassException {
        this.cl = cl;
        this.resolveEx = resolveEx;
        this.superDesc = superDesc;
        name = model.name;
        suid = new Long(model.getSerialVersionUID());
        isProxy = false;
        isEnum = model.isEnum;
        serializable = model.serializable;
        externalizable = model.externalizable;
        hasBlockExternalData = model.hasBlockExternalData;
        hasWriteObjectData = model.hasWriteObjectData;
        fields = model.fields;
        primDataSize = model.primDataSize;
        numObjFields = model.numObjFields;
        if (cl != null) {
            localDesc = lookup(cl, true);
            if (localDesc.isProxy) {
                throw new InvalidClassException("cannot bind non-proxy descriptor to a proxy class");
            }
            if (isEnum != localDesc.isEnum) {
                throw new InvalidClassException(isEnum ? "cannot bind enum descriptor to a non-enum class" : "cannot bind non-enum descriptor to an enum class");
            }
            if (serializable == localDesc.serializable && !cl.isArray() && suid.longValue() != localDesc.getSerialVersionUID()) {
                throw new InvalidClassException(localDesc.name, "local class incompatible: " + "stream classdesc serialVersionUID = " + suid + ", local class serialVersionUID = " + localDesc.getSerialVersionUID());
            }
            if (!classNamesEqual(name, localDesc.name)) {
                throw new InvalidClassException(localDesc.name, "local class name incompatible with stream class " + "name \"" + name + "\"");
            }
            if (!isEnum) {
                if ((serializable == localDesc.serializable) && (externalizable != localDesc.externalizable)) {
                    throw new InvalidClassException(localDesc.name, "Serializable incompatible with Externalizable");
                }
                if ((serializable != localDesc.serializable) || (externalizable != localDesc.externalizable) || !(serializable || externalizable)) {
                    deserializeEx = new InvalidClassException(localDesc.name, "class invalid for deserialization");
                }
            }
            cons = localDesc.cons;
            writeObjectMethod = localDesc.writeObjectMethod;
            readObjectMethod = localDesc.readObjectMethod;
            readObjectNoDataMethod = localDesc.readObjectNoDataMethod;
            writeReplaceMethod = localDesc.writeReplaceMethod;
            readResolveMethod = localDesc.readResolveMethod;
            if (deserializeEx == null) {
                deserializeEx = localDesc.deserializeEx;
            }
        }
        fieldRefl = getReflector(fields, localDesc);
        fields = fieldRefl.getFields();
    }
    
    void readNonProxy(ObjectInputStream in) throws IOException, ClassNotFoundException {
        name = in.readUTF();
        suid = new Long(in.readLong());
        isProxy = false;
        byte flags = in.readByte();
        hasWriteObjectData = ((flags & ObjectStreamConstants.SC_WRITE_METHOD) != 0);
        hasBlockExternalData = ((flags & ObjectStreamConstants.SC_BLOCK_DATA) != 0);
        externalizable = ((flags & ObjectStreamConstants.SC_EXTERNALIZABLE) != 0);
        boolean sflag = ((flags & ObjectStreamConstants.SC_SERIALIZABLE) != 0);
        if (externalizable && sflag) {
            throw new InvalidClassException(name, "serializable and externalizable flags conflict");
        }
        serializable = externalizable || sflag;
        isEnum = ((flags & ObjectStreamConstants.SC_ENUM) != 0);
        if (isEnum && suid.longValue() != 0L) {
            throw new InvalidClassException(name, "enum descriptor has non-zero serialVersionUID: " + suid);
        }
        int numFields = in.readShort();
        if (isEnum && numFields != 0) {
            throw new InvalidClassException(name, "enum descriptor has non-zero field count: " + numFields);
        }
        fields = (numFields > 0) ? new ObjectStreamField[numFields] : NO_FIELDS;
        for (int i = 0; i < numFields; i++) {
            char tcode = (char)in.readByte();
            String fname = in.readUTF();
            String signature = ((tcode == 'L') || (tcode == '[')) ? in.readTypeString() : new String(new char[]{tcode});
            try {
                fields[i] = new ObjectStreamField(fname, signature, false);
            } catch (RuntimeException e) {
                throw (IOException)(IOException)new InvalidClassException(name, "invalid descriptor for field " + fname).initCause(e);
            }
        }
        computeFieldOffsets();
    }
    
    void writeNonProxy(ObjectOutputStream out) throws IOException {
        out.writeUTF(name);
        out.writeLong(getSerialVersionUID());
        byte flags = 0;
        if (externalizable) {
            flags |= ObjectStreamConstants.SC_EXTERNALIZABLE;
            int protocol = out.getProtocolVersion();
            if (protocol != ObjectStreamConstants.PROTOCOL_VERSION_1) {
                flags |= ObjectStreamConstants.SC_BLOCK_DATA;
            }
        } else if (serializable) {
            flags |= ObjectStreamConstants.SC_SERIALIZABLE;
        }
        if (hasWriteObjectData) {
            flags |= ObjectStreamConstants.SC_WRITE_METHOD;
        }
        if (isEnum) {
            flags |= ObjectStreamConstants.SC_ENUM;
        }
        out.writeByte(flags);
        out.writeShort(fields.length);
        for (int i = 0; i < fields.length; i++) {
            ObjectStreamField f = fields[i];
            out.writeByte(f.getTypeCode());
            out.writeUTF(f.getName());
            if (!f.isPrimitive()) {
                out.writeTypeString(f.getTypeString());
            }
        }
    }
    
    ClassNotFoundException getResolveException() {
        return resolveEx;
    }
    
    void checkDeserialize() throws InvalidClassException {
        if (deserializeEx != null) {
            throw deserializeEx;
        }
    }
    
    void checkSerialize() throws InvalidClassException {
        if (serializeEx != null) {
            throw serializeEx;
        }
    }
    
    void checkDefaultSerialize() throws InvalidClassException {
        if (defaultSerializeEx != null) {
            throw defaultSerializeEx;
        }
    }
    
    ObjectStreamClass getSuperDesc() {
        return superDesc;
    }
    
    ObjectStreamClass getLocalDesc() {
        return localDesc;
    }
    
    ObjectStreamField[] getFields(boolean copy) {
        return copy ? (ObjectStreamField[])(ObjectStreamField[])fields.clone() : fields;
    }
    
    ObjectStreamField getField(String name, Class type) {
        for (int i = 0; i < fields.length; i++) {
            ObjectStreamField f = fields[i];
            if (f.getName().equals(name)) {
                if (type == null || (type == Object.class && !f.isPrimitive())) {
                    return f;
                }
                Class ftype = f.getType();
                if (ftype != null && type.isAssignableFrom(ftype)) {
                    return f;
                }
            }
        }
        return null;
    }
    
    boolean isProxy() {
        return isProxy;
    }
    
    boolean isEnum() {
        return isEnum;
    }
    
    boolean isExternalizable() {
        return externalizable;
    }
    
    boolean isSerializable() {
        return serializable;
    }
    
    boolean hasBlockExternalData() {
        return hasBlockExternalData;
    }
    
    boolean hasWriteObjectData() {
        return hasWriteObjectData;
    }
    
    boolean isInstantiable() {
        return (cons != null);
    }
    
    boolean hasWriteObjectMethod() {
        return (writeObjectMethod != null);
    }
    
    boolean hasReadObjectMethod() {
        return (readObjectMethod != null);
    }
    
    boolean hasReadObjectNoDataMethod() {
        return (readObjectNoDataMethod != null);
    }
    
    boolean hasWriteReplaceMethod() {
        return (writeReplaceMethod != null);
    }
    
    boolean hasReadResolveMethod() {
        return (readResolveMethod != null);
    }
    
    Object newInstance() throws InstantiationException, InvocationTargetException, UnsupportedOperationException {
        if (cons != null) {
            try {
                return cons.newInstance(null);
            } catch (IllegalAccessException ex) {
                throw new InternalError();
            }
        } else {
            throw new UnsupportedOperationException();
        }
    }
    
    void invokeWriteObject(Object obj, ObjectOutputStream out) throws IOException, UnsupportedOperationException {
        if (writeObjectMethod != null) {
            try {
                writeObjectMethod.invoke(obj, new Object[]{out});
            } catch (InvocationTargetException ex) {
                Throwable th = ex.getTargetException();
                if (th instanceof IOException) {
                    throw (IOException)(IOException)th;
                } else {
                    throwMiscException(th);
                }
            } catch (IllegalAccessException ex) {
                throw new InternalError();
            }
        } else {
            throw new UnsupportedOperationException();
        }
    }
    
    void invokeReadObject(Object obj, ObjectInputStream in) throws ClassNotFoundException, IOException, UnsupportedOperationException {
        if (readObjectMethod != null) {
            try {
                readObjectMethod.invoke(obj, new Object[]{in});
            } catch (InvocationTargetException ex) {
                Throwable th = ex.getTargetException();
                if (th instanceof ClassNotFoundException) {
                    throw (ClassNotFoundException)(ClassNotFoundException)th;
                } else if (th instanceof IOException) {
                    throw (IOException)(IOException)th;
                } else {
                    throwMiscException(th);
                }
            } catch (IllegalAccessException ex) {
                throw new InternalError();
            }
        } else {
            throw new UnsupportedOperationException();
        }
    }
    
    void invokeReadObjectNoData(Object obj) throws IOException, UnsupportedOperationException {
        if (readObjectNoDataMethod != null) {
            try {
                readObjectNoDataMethod.invoke(obj, null);
            } catch (InvocationTargetException ex) {
                Throwable th = ex.getTargetException();
                if (th instanceof ObjectStreamException) {
                    throw (ObjectStreamException)(ObjectStreamException)th;
                } else {
                    throwMiscException(th);
                }
            } catch (IllegalAccessException ex) {
                throw new InternalError();
            }
        } else {
            throw new UnsupportedOperationException();
        }
    }
    
    Object invokeWriteReplace(Object obj) throws IOException, UnsupportedOperationException {
        if (writeReplaceMethod != null) {
            try {
                return writeReplaceMethod.invoke(obj, null);
            } catch (InvocationTargetException ex) {
                Throwable th = ex.getTargetException();
                if (th instanceof ObjectStreamException) {
                    throw (ObjectStreamException)(ObjectStreamException)th;
                } else {
                    throwMiscException(th);
                    throw new InternalError();
                }
            } catch (IllegalAccessException ex) {
                throw new InternalError();
            }
        } else {
            throw new UnsupportedOperationException();
        }
    }
    
    Object invokeReadResolve(Object obj) throws IOException, UnsupportedOperationException {
        if (readResolveMethod != null) {
            try {
                return readResolveMethod.invoke(obj, null);
            } catch (InvocationTargetException ex) {
                Throwable th = ex.getTargetException();
                if (th instanceof ObjectStreamException) {
                    throw (ObjectStreamException)(ObjectStreamException)th;
                } else {
                    throwMiscException(th);
                    throw new InternalError();
                }
            } catch (IllegalAccessException ex) {
                throw new InternalError();
            }
        } else {
            throw new UnsupportedOperationException();
        }
    }
    {
    }
    
    ObjectStreamClass$ClassDataSlot[] getClassDataLayout() throws InvalidClassException {
        if (dataLayout == null) {
            dataLayout = getClassDataLayout0();
        }
        return dataLayout;
    }
    
    private ObjectStreamClass$ClassDataSlot[] getClassDataLayout0() throws InvalidClassException {
        ArrayList slots = new ArrayList();
        Class start = cl;
        Class end = cl;
        while (end != null && Serializable.class.isAssignableFrom(end)) {
            end = end.getSuperclass();
        }
        for (ObjectStreamClass d = this; d != null; d = d.superDesc) {
            String searchName = (d.cl != null) ? d.cl.getName() : d.name;
            Class match = null;
            for (Class c = start; c != end; c = c.getSuperclass()) {
                if (searchName.equals(c.getName())) {
                    match = c;
                    break;
                }
            }
            if (match != null) {
                for (Class c = start; c != match; c = c.getSuperclass()) {
                    slots.add(new ObjectStreamClass$ClassDataSlot(ObjectStreamClass.lookup(c, true), false));
                }
                start = match.getSuperclass();
            }
            slots.add(new ObjectStreamClass$ClassDataSlot(d.getVariantFor(match), true));
        }
        for (Class c = start; c != end; c = c.getSuperclass()) {
            slots.add(new ObjectStreamClass$ClassDataSlot(ObjectStreamClass.lookup(c, true), false));
        }
        Collections.reverse(slots);
        return (ObjectStreamClass$ClassDataSlot[])(ObjectStreamClass$ClassDataSlot[])slots.toArray(new ObjectStreamClass$ClassDataSlot[slots.size()]);
    }
    
    int getPrimDataSize() {
        return primDataSize;
    }
    
    int getNumObjFields() {
        return numObjFields;
    }
    
    void getPrimFieldValues(Object obj, byte[] buf) {
        fieldRefl.getPrimFieldValues(obj, buf);
    }
    
    void setPrimFieldValues(Object obj, byte[] buf) {
        fieldRefl.setPrimFieldValues(obj, buf);
    }
    
    void getObjFieldValues(Object obj, Object[] vals) {
        fieldRefl.getObjFieldValues(obj, vals);
    }
    
    void setObjFieldValues(Object obj, Object[] vals) {
        fieldRefl.setObjFieldValues(obj, vals);
    }
    
    private void computeFieldOffsets() throws InvalidClassException {
        primDataSize = 0;
        numObjFields = 0;
        int firstObjIndex = -1;
        for (int i = 0; i < fields.length; i++) {
            ObjectStreamField f = fields[i];
            switch (f.getTypeCode()) {
            case 'Z': 
            
            case 'B': 
                f.setOffset(primDataSize++);
                break;
            
            case 'C': 
            
            case 'S': 
                f.setOffset(primDataSize);
                primDataSize += 2;
                break;
            
            case 'I': 
            
            case 'F': 
                f.setOffset(primDataSize);
                primDataSize += 4;
                break;
            
            case 'J': 
            
            case 'D': 
                f.setOffset(primDataSize);
                primDataSize += 8;
                break;
            
            case '[': 
            
            case 'L': 
                f.setOffset(numObjFields++);
                if (firstObjIndex == -1) {
                    firstObjIndex = i;
                }
                break;
            
            default: 
                throw new InternalError();
            
            }
        }
        if (firstObjIndex != -1 && firstObjIndex + numObjFields != fields.length) {
            throw new InvalidClassException(name, "illegal field order");
        }
    }
    
    private ObjectStreamClass getVariantFor(Class cl) throws InvalidClassException {
        if (this.cl == cl) {
            return this;
        }
        ObjectStreamClass desc = new ObjectStreamClass();
        if (isProxy) {
            desc.initProxy(cl, null, superDesc);
        } else {
            desc.initNonProxy(this, cl, null, superDesc);
        }
        return desc;
    }
    
    private static Constructor getExternalizableConstructor(Class cl) {
        try {
            Constructor cons = cl.getDeclaredConstructor(new Class[0]);
            cons.setAccessible(true);
            return ((cons.getModifiers() & Modifier.PUBLIC) != 0) ? cons : null;
        } catch (NoSuchMethodException ex) {
            return null;
        }
    }
    
    private static Constructor getSerializableConstructor(Class cl) {
        Class initCl = cl;
        while (Serializable.class.isAssignableFrom(initCl)) {
            if ((initCl = initCl.getSuperclass()) == null) {
                return null;
            }
        }
        try {
            Constructor cons = initCl.getDeclaredConstructor(new Class[0]);
            int mods = cons.getModifiers();
            if ((mods & Modifier.PRIVATE) != 0 || ((mods & (Modifier.PUBLIC | Modifier.PROTECTED)) == 0 && !packageEquals(cl, initCl))) {
                return null;
            }
            cons = reflFactory.newConstructorForSerialization(cl, cons);
            cons.setAccessible(true);
            return cons;
        } catch (NoSuchMethodException ex) {
            return null;
        }
    }
    
    private static Method getInheritableMethod(Class cl, String name, Class[] argTypes, Class returnType) {
        Method meth = null;
        Class defCl = cl;
        while (defCl != null) {
            try {
                meth = defCl.getDeclaredMethod(name, argTypes);
                break;
            } catch (NoSuchMethodException ex) {
                defCl = defCl.getSuperclass();
            }
        }
        if ((meth == null) || (meth.getReturnType() != returnType)) {
            return null;
        }
        meth.setAccessible(true);
        int mods = meth.getModifiers();
        if ((mods & (Modifier.STATIC | Modifier.ABSTRACT)) != 0) {
            return null;
        } else if ((mods & (Modifier.PUBLIC | Modifier.PROTECTED)) != 0) {
            return meth;
        } else if ((mods & Modifier.PRIVATE) != 0) {
            return (cl == defCl) ? meth : null;
        } else {
            return packageEquals(cl, defCl) ? meth : null;
        }
    }
    
    private static Method getPrivateMethod(Class cl, String name, Class[] argTypes, Class returnType) {
        try {
            Method meth = cl.getDeclaredMethod(name, argTypes);
            meth.setAccessible(true);
            int mods = meth.getModifiers();
            return ((meth.getReturnType() == returnType) && ((mods & Modifier.STATIC) == 0) && ((mods & Modifier.PRIVATE) != 0)) ? meth : null;
        } catch (NoSuchMethodException ex) {
            return null;
        }
    }
    
    private static boolean packageEquals(Class cl1, Class cl2) {
        return (cl1.getClassLoader() == cl2.getClassLoader() && getPackageName(cl1).equals(getPackageName(cl2)));
    }
    
    private static String getPackageName(Class cl) {
        String s = cl.getName();
        int i = s.lastIndexOf('[');
        if (i >= 0) {
            s = s.substring(i + 2);
        }
        i = s.lastIndexOf('.');
        return (i >= 0) ? s.substring(0, i) : "";
    }
    
    private static boolean classNamesEqual(String name1, String name2) {
        name1 = name1.substring(name1.lastIndexOf('.') + 1);
        name2 = name2.substring(name2.lastIndexOf('.') + 1);
        return name1.equals(name2);
    }
    
    static String getClassSignature(Class cl) {
        StringBuffer sbuf = new StringBuffer();
        while (cl.isArray()) {
            sbuf.append('[');
            cl = cl.getComponentType();
        }
        if (cl.isPrimitive()) {
            if (cl == Integer.TYPE) {
                sbuf.append('I');
            } else if (cl == Byte.TYPE) {
                sbuf.append('B');
            } else if (cl == Long.TYPE) {
                sbuf.append('J');
            } else if (cl == Float.TYPE) {
                sbuf.append('F');
            } else if (cl == Double.TYPE) {
                sbuf.append('D');
            } else if (cl == Short.TYPE) {
                sbuf.append('S');
            } else if (cl == Character.TYPE) {
                sbuf.append('C');
            } else if (cl == Boolean.TYPE) {
                sbuf.append('Z');
            } else if (cl == Void.TYPE) {
                sbuf.append('V');
            } else {
                throw new InternalError();
            }
        } else {
            sbuf.append('L' + cl.getName().replace('.', '/') + ';');
        }
        return sbuf.toString();
    }
    
    private static String getMethodSignature(Class[] paramTypes, Class retType) {
        StringBuffer sbuf = new StringBuffer();
        sbuf.append('(');
        for (int i = 0; i < paramTypes.length; i++) {
            sbuf.append(getClassSignature(paramTypes[i]));
        }
        sbuf.append(')');
        sbuf.append(getClassSignature(retType));
        return sbuf.toString();
    }
    
    private static void throwMiscException(Throwable th) throws IOException {
        if (th instanceof RuntimeException) {
            throw (RuntimeException)(RuntimeException)th;
        } else if (th instanceof Error) {
            throw (Error)(Error)th;
        } else {
            IOException ex = new IOException("unexpected exception type");
            ex.initCause(th);
            throw ex;
        }
    }
    
    private static ObjectStreamField[] getSerialFields(Class cl) throws InvalidClassException {
        ObjectStreamField[] fields;
        if (Serializable.class.isAssignableFrom(cl) && !Externalizable.class.isAssignableFrom(cl) && !Proxy.isProxyClass(cl) && !cl.isInterface()) {
            if ((fields = getDeclaredSerialFields(cl)) == null) {
                fields = getDefaultSerialFields(cl);
            }
            Arrays.sort(fields);
        } else {
            fields = NO_FIELDS;
        }
        return fields;
    }
    
    private static ObjectStreamField[] getDeclaredSerialFields(Class cl) throws InvalidClassException {
        ObjectStreamField[] serialPersistentFields = null;
        try {
            Field f = cl.getDeclaredField("serialPersistentFields");
            int mask = Modifier.PRIVATE | Modifier.STATIC | Modifier.FINAL;
            if ((f.getModifiers() & mask) == mask) {
                f.setAccessible(true);
                serialPersistentFields = (ObjectStreamField[])(ObjectStreamField[])f.get(null);
            }
        } catch (Exception ex) {
        }
        if (serialPersistentFields == null) {
            return null;
        } else if (serialPersistentFields.length == 0) {
            return NO_FIELDS;
        }
        ObjectStreamField[] boundFields = new ObjectStreamField[serialPersistentFields.length];
        Set fieldNames = new HashSet(serialPersistentFields.length);
        for (int i = 0; i < serialPersistentFields.length; i++) {
            ObjectStreamField spf = serialPersistentFields[i];
            String fname = spf.getName();
            if (fieldNames.contains(fname)) {
                throw new InvalidClassException("multiple serializable fields named " + fname);
            }
            fieldNames.add(fname);
            try {
                Field f = cl.getDeclaredField(fname);
                if ((f.getType() == spf.getType()) && ((f.getModifiers() & Modifier.STATIC) == 0)) {
                    boundFields[i] = new ObjectStreamField(f, spf.isUnshared(), true);
                }
            } catch (NoSuchFieldException ex) {
            }
            if (boundFields[i] == null) {
                boundFields[i] = new ObjectStreamField(fname, spf.getType(), spf.isUnshared());
            }
        }
        return boundFields;
    }
    
    private static ObjectStreamField[] getDefaultSerialFields(Class cl) {
        Field[] clFields = cl.getDeclaredFields();
        ArrayList list = new ArrayList();
        int mask = Modifier.STATIC | Modifier.TRANSIENT;
        for (int i = 0; i < clFields.length; i++) {
            if ((clFields[i].getModifiers() & mask) == 0) {
                list.add(new ObjectStreamField(clFields[i], false, true));
            }
        }
        int size = list.size();
        return (size == 0) ? NO_FIELDS : (ObjectStreamField[])(ObjectStreamField[])list.toArray(new ObjectStreamField[size]);
    }
    
    private static Long getDeclaredSUID(Class cl) {
        try {
            Field f = cl.getDeclaredField("serialVersionUID");
            int mask = Modifier.STATIC | Modifier.FINAL;
            if ((f.getModifiers() & mask) == mask) {
                f.setAccessible(true);
                return new Long(f.getLong(null));
            }
        } catch (Exception ex) {
        }
        return null;
    }
    
    private static long computeDefaultSUID(Class cl) {
        if (!Serializable.class.isAssignableFrom(cl) || Proxy.isProxyClass(cl)) {
            return 0L;
        }
        try {
            ByteArrayOutputStream bout = new ByteArrayOutputStream();
            DataOutputStream dout = new DataOutputStream(bout);
            dout.writeUTF(cl.getName());
            int classMods = cl.getModifiers() & (Modifier.PUBLIC | Modifier.FINAL | Modifier.INTERFACE | Modifier.ABSTRACT);
            Method[] methods = cl.getDeclaredMethods();
            if ((classMods & Modifier.INTERFACE) != 0) {
                classMods = (methods.length > 0) ? (classMods | Modifier.ABSTRACT) : (classMods & ~Modifier.ABSTRACT);
            }
            dout.writeInt(classMods);
            if (!cl.isArray()) {
                Class[] interfaces = cl.getInterfaces();
                String[] ifaceNames = new String[interfaces.length];
                for (int i = 0; i < interfaces.length; i++) {
                    ifaceNames[i] = interfaces[i].getName();
                }
                Arrays.sort(ifaceNames);
                for (int i = 0; i < ifaceNames.length; i++) {
                    dout.writeUTF(ifaceNames[i]);
                }
            }
            Field[] fields = cl.getDeclaredFields();
            ObjectStreamClass$MemberSignature[] fieldSigs = new ObjectStreamClass$MemberSignature[fields.length];
            for (int i = 0; i < fields.length; i++) {
                fieldSigs[i] = new ObjectStreamClass$MemberSignature(fields[i]);
            }
            Arrays.sort(fieldSigs, new ObjectStreamClass$3());
            for (int i = 0; i < fieldSigs.length; i++) {
                ObjectStreamClass$MemberSignature sig = fieldSigs[i];
                int mods = sig.member.getModifiers() & (Modifier.PUBLIC | Modifier.PRIVATE | Modifier.PROTECTED | Modifier.STATIC | Modifier.FINAL | Modifier.VOLATILE | Modifier.TRANSIENT);
                if (((mods & Modifier.PRIVATE) == 0) || ((mods & (Modifier.STATIC | Modifier.TRANSIENT)) == 0)) {
                    dout.writeUTF(sig.name);
                    dout.writeInt(mods);
                    dout.writeUTF(sig.signature);
                }
            }
            if (hasStaticInitializer(cl)) {
                dout.writeUTF("<clinit>");
                dout.writeInt(Modifier.STATIC);
                dout.writeUTF("()V");
            }
            Constructor[] cons = cl.getDeclaredConstructors();
            ObjectStreamClass$MemberSignature[] consSigs = new ObjectStreamClass$MemberSignature[cons.length];
            for (int i = 0; i < cons.length; i++) {
                consSigs[i] = new ObjectStreamClass$MemberSignature(cons[i]);
            }
            Arrays.sort(consSigs, new ObjectStreamClass$4());
            for (int i = 0; i < consSigs.length; i++) {
                ObjectStreamClass$MemberSignature sig = consSigs[i];
                int mods = sig.member.getModifiers() & (Modifier.PUBLIC | Modifier.PRIVATE | Modifier.PROTECTED | Modifier.STATIC | Modifier.FINAL | Modifier.SYNCHRONIZED | Modifier.NATIVE | Modifier.ABSTRACT | Modifier.STRICT);
                if ((mods & Modifier.PRIVATE) == 0) {
                    dout.writeUTF("<init>");
                    dout.writeInt(mods);
                    dout.writeUTF(sig.signature.replace('/', '.'));
                }
            }
            ObjectStreamClass$MemberSignature[] methSigs = new ObjectStreamClass$MemberSignature[methods.length];
            for (int i = 0; i < methods.length; i++) {
                methSigs[i] = new ObjectStreamClass$MemberSignature(methods[i]);
            }
            Arrays.sort(methSigs, new ObjectStreamClass$5());
            for (int i = 0; i < methSigs.length; i++) {
                ObjectStreamClass$MemberSignature sig = methSigs[i];
                int mods = sig.member.getModifiers() & (Modifier.PUBLIC | Modifier.PRIVATE | Modifier.PROTECTED | Modifier.STATIC | Modifier.FINAL | Modifier.SYNCHRONIZED | Modifier.NATIVE | Modifier.ABSTRACT | Modifier.STRICT);
                if ((mods & Modifier.PRIVATE) == 0) {
                    dout.writeUTF(sig.name);
                    dout.writeInt(mods);
                    dout.writeUTF(sig.signature.replace('/', '.'));
                }
            }
            dout.flush();
            MessageDigest md = MessageDigest.getInstance("SHA");
            byte[] hashBytes = md.digest(bout.toByteArray());
            long hash = 0;
            for (int i = Math.min(hashBytes.length, 8) - 1; i >= 0; i--) {
                hash = (hash << 8) | (hashBytes[i] & 255);
            }
            return hash;
        } catch (IOException ex) {
            throw new InternalError();
        } catch (NoSuchAlgorithmException ex) {
            throw new SecurityException(ex.getMessage());
        }
    }
    
    private static native boolean hasStaticInitializer(Class cl);
    {
    }
    {
    }
    
    private static ObjectStreamClass$FieldReflector getReflector(ObjectStreamField[] fields, ObjectStreamClass localDesc) throws InvalidClassException {
        Class cl = (localDesc != null && fields.length > 0) ? localDesc.cl : null;
        processQueue(ObjectStreamClass$Caches.access$2500(), ObjectStreamClass$Caches.reflectors);
        ObjectStreamClass$FieldReflectorKey key = new ObjectStreamClass$FieldReflectorKey(cl, fields, ObjectStreamClass$Caches.access$2500());
        Reference ref = (Reference)ObjectStreamClass$Caches.reflectors.get(key);
        Object entry = null;
        if (ref != null) {
            entry = ref.get();
        }
        ObjectStreamClass$EntryFuture future = null;
        if (entry == null) {
            ObjectStreamClass$EntryFuture newEntry = new ObjectStreamClass$EntryFuture(null);
            Reference newRef = new SoftReference(newEntry);
            do {
                if (ref != null) {
                    ObjectStreamClass$Caches.reflectors.remove(key, ref);
                }
                ref = (Reference)ObjectStreamClass$Caches.reflectors.putIfAbsent(key, newRef);
                if (ref != null) {
                    entry = ref.get();
                }
            }             while (ref != null && entry == null);
            if (entry == null) {
                future = newEntry;
            }
        }
        if (entry instanceof ObjectStreamClass$FieldReflector) {
            return (ObjectStreamClass$FieldReflector)(ObjectStreamClass$FieldReflector)entry;
        } else if (entry instanceof ObjectStreamClass$EntryFuture) {
            entry = ((ObjectStreamClass$EntryFuture)(ObjectStreamClass$EntryFuture)entry).get();
        } else if (entry == null) {
            try {
                entry = new ObjectStreamClass$FieldReflector(matchFields(fields, localDesc));
            } catch (Throwable th) {
                entry = th;
            }
            future.set(entry);
            ObjectStreamClass$Caches.reflectors.put(key, new SoftReference(entry));
        }
        if (entry instanceof ObjectStreamClass$FieldReflector) {
            return (ObjectStreamClass$FieldReflector)(ObjectStreamClass$FieldReflector)entry;
        } else if (entry instanceof InvalidClassException) {
            throw (InvalidClassException)(InvalidClassException)entry;
        } else if (entry instanceof RuntimeException) {
            throw (RuntimeException)(RuntimeException)entry;
        } else if (entry instanceof Error) {
            throw (Error)(Error)entry;
        } else {
            throw new InternalError("unexpected entry: " + entry);
        }
    }
    {
    }
    
    private static ObjectStreamField[] matchFields(ObjectStreamField[] fields, ObjectStreamClass localDesc) throws InvalidClassException {
        ObjectStreamField[] localFields = (localDesc != null) ? localDesc.fields : NO_FIELDS;
        ObjectStreamField[] matches = new ObjectStreamField[fields.length];
        for (int i = 0; i < fields.length; i++) {
            ObjectStreamField f = fields[i];
            ObjectStreamField m = null;
            for (int j = 0; j < localFields.length; j++) {
                ObjectStreamField lf = localFields[j];
                if (f.getName().equals(lf.getName())) {
                    if ((f.isPrimitive() || lf.isPrimitive()) && f.getTypeCode() != lf.getTypeCode()) {
                        throw new InvalidClassException(localDesc.name, "incompatible types for field " + f.getName());
                    }
                    if (lf.getField() != null) {
                        m = new ObjectStreamField(lf.getField(), lf.isUnshared(), false);
                    } else {
                        m = new ObjectStreamField(lf.getName(), lf.getSignature(), lf.isUnshared());
                    }
                }
            }
            if (m == null) {
                m = new ObjectStreamField(f.getName(), f.getSignature(), false);
            }
            m.setOffset(f.getOffset());
            matches[i] = m;
        }
        return matches;
    }
    
    static void processQueue(ReferenceQueue queue, ConcurrentMap map) {
        Reference ref;
        while ((ref = queue.poll()) != null) {
            map.remove(ref);
        }
    }
    {
    }
}
