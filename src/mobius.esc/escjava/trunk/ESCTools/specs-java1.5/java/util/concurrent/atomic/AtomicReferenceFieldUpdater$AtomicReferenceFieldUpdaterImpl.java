package java.util.concurrent.atomic;

import sun.misc.Unsafe;
import java.lang.reflect.*;

class AtomicReferenceFieldUpdater$AtomicReferenceFieldUpdaterImpl extends AtomicReferenceFieldUpdater {
    private static final Unsafe unsafe = Unsafe.getUnsafe();
    private final long offset;
    private final Class tclass;
    private final Class vclass;
    private final Class cclass;
    
    AtomicReferenceFieldUpdater$AtomicReferenceFieldUpdaterImpl(Class tclass, Class vclass, String fieldName) {
        
        Field field = null;
        Class fieldClass = null;
        Class caller = null;
        int modifiers = 0;
        try {
            field = tclass.getDeclaredField(fieldName);
            caller = sun.reflect.Reflection.getCallerClass(3);
            modifiers = field.getModifiers();
            sun.reflect.misc.ReflectUtil.ensureMemberAccess(caller, tclass, null, modifiers);
            sun.reflect.misc.ReflectUtil.checkPackageAccess(tclass);
            fieldClass = field.getType();
        } catch (Exception ex) {
            throw new RuntimeException(ex);
        }
        if (vclass != fieldClass) throw new ClassCastException();
        if (!Modifier.isVolatile(modifiers)) throw new IllegalArgumentException("Must be volatile type");
        this.cclass = (Modifier.isProtected(modifiers) && caller != tclass) ? caller : null;
        this.tclass = tclass;
        this.vclass = vclass;
        offset = unsafe.objectFieldOffset(field);
    }
    
    public boolean compareAndSet(Object obj, Object expect, Object update) {
        if (!tclass.isInstance(obj) || (update != null && !vclass.isInstance(update))) throw new ClassCastException();
        if (cclass != null) ensureProtectedAccess(obj);
        return unsafe.compareAndSwapObject(obj, offset, expect, update);
    }
    
    public boolean weakCompareAndSet(Object obj, Object expect, Object update) {
        if (!tclass.isInstance(obj) || (update != null && !vclass.isInstance(update))) throw new ClassCastException();
        if (cclass != null) ensureProtectedAccess(obj);
        return unsafe.compareAndSwapObject(obj, offset, expect, update);
    }
    
    public void set(Object obj, Object newValue) {
        if (!tclass.isInstance(obj) || (newValue != null && !vclass.isInstance(newValue))) throw new ClassCastException();
        if (cclass != null) ensureProtectedAccess(obj);
        unsafe.putObjectVolatile(obj, offset, newValue);
    }
    
    public Object get(Object obj) {
        if (!tclass.isInstance(obj)) throw new ClassCastException();
        if (cclass != null) ensureProtectedAccess(obj);
        return (Object)unsafe.getObjectVolatile(obj, offset);
    }
    
    private void ensureProtectedAccess(Object obj) {
        if (cclass.isInstance(obj)) {
            return;
        }
        throw new RuntimeException(new IllegalAccessException("Class " + cclass.getName() + " can not access a protected member of class " + tclass.getName() + " using an instance of " + obj.getClass().getName()));
    }
}
