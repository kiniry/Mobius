package java.util.concurrent.atomic;

import sun.misc.Unsafe;
import java.lang.reflect.*;

class AtomicLongFieldUpdater$LockedUpdater extends AtomicLongFieldUpdater {
    private static final Unsafe unsafe = Unsafe.getUnsafe();
    private final long offset;
    private final Class tclass;
    private final Class cclass;
    
    AtomicLongFieldUpdater$LockedUpdater(Class tclass, String fieldName) {
        
        Field field = null;
        Class caller = null;
        int modifiers = 0;
        try {
            field = tclass.getDeclaredField(fieldName);
            caller = sun.reflect.Reflection.getCallerClass(3);
            modifiers = field.getModifiers();
            sun.reflect.misc.ReflectUtil.ensureMemberAccess(caller, tclass, null, modifiers);
            sun.reflect.misc.ReflectUtil.checkPackageAccess(tclass);
        } catch (Exception ex) {
            throw new RuntimeException(ex);
        }
        Class fieldt = field.getType();
        if (fieldt != Long.TYPE) throw new IllegalArgumentException("Must be long type");
        if (!Modifier.isVolatile(modifiers)) throw new IllegalArgumentException("Must be volatile type");
        this.cclass = (Modifier.isProtected(modifiers) && caller != tclass) ? caller : null;
        this.tclass = tclass;
        offset = unsafe.objectFieldOffset(field);
    }
    
    public boolean compareAndSet(Object obj, long expect, long update) {
        if (!tclass.isInstance(obj)) throw new ClassCastException();
        if (cclass != null) ensureProtectedAccess(obj);
        synchronized (this) {
            long v = unsafe.getLong(obj, offset);
            if (v != expect) return false;
            unsafe.putLong(obj, offset, update);
            return true;
        }
    }
    
    public boolean weakCompareAndSet(Object obj, long expect, long update) {
        return compareAndSet(obj, expect, update);
    }
    
    public void set(Object obj, long newValue) {
        if (!tclass.isInstance(obj)) throw new ClassCastException();
        if (cclass != null) ensureProtectedAccess(obj);
        synchronized (this) {
            unsafe.putLong(obj, offset, newValue);
        }
    }
    
    public long get(Object obj) {
        if (!tclass.isInstance(obj)) throw new ClassCastException();
        if (cclass != null) ensureProtectedAccess(obj);
        synchronized (this) {
            return unsafe.getLong(obj, offset);
        }
    }
    
    private void ensureProtectedAccess(Object obj) {
        if (cclass.isInstance(obj)) {
            return;
        }
        throw new RuntimeException(new IllegalAccessException("Class " + cclass.getName() + " can not access a protected member of class " + tclass.getName() + " using an instance of " + obj.getClass().getName()));
    }
}
