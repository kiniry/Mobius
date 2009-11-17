package java.lang.reflect;

import sun.reflect.FieldAccessor;
import sun.reflect.Reflection;
import sun.reflect.generics.repository.FieldRepository;
import sun.reflect.generics.factory.CoreReflectionFactory;
import sun.reflect.generics.factory.GenericsFactory;
import sun.reflect.generics.scope.ClassScope;
import java.lang.annotation.Annotation;
import java.util.Map;
import sun.reflect.annotation.AnnotationParser;

public final class Field extends AccessibleObject implements Member {
    private Class clazz;
    private int slot;
    private String name;
    private Class type;
    private int modifiers;
    private transient String signature;
    private transient FieldRepository genericInfo;
    private byte[] annotations;
    private FieldAccessor fieldAccessor;
    private FieldAccessor overrideFieldAccessor;
    private Field root;
    private volatile Class securityCheckTargetClassCache;
    
    private String getGenericSignature() {
        return signature;
    }
    
    private GenericsFactory getFactory() {
        Class c = getDeclaringClass();
        return CoreReflectionFactory.make(c, ClassScope.make(c));
    }
    
    private FieldRepository getGenericInfo() {
        if (genericInfo == null) {
            genericInfo = FieldRepository.make(getGenericSignature(), getFactory());
        }
        return genericInfo;
    }
    
    Field(Class declaringClass, String name, Class type, int modifiers, int slot, String signature, byte[] annotations) {
        
        this.clazz = declaringClass;
        this.name = name;
        this.type = type;
        this.modifiers = modifiers;
        this.slot = slot;
        this.signature = signature;
        this.annotations = annotations;
    }
    
    Field copy() {
        Field res = new Field(clazz, name, type, modifiers, slot, signature, annotations);
        res.root = this;
        res.fieldAccessor = fieldAccessor;
        res.overrideFieldAccessor = overrideFieldAccessor;
        return res;
    }
    
    public Class getDeclaringClass() {
        return clazz;
    }
    
    public String getName() {
        return name;
    }
    
    public int getModifiers() {
        return modifiers;
    }
    
    public boolean isEnumConstant() {
        return (getModifiers() & Modifier.ENUM) != 0;
    }
    
    public boolean isSynthetic() {
        return Modifier.isSynthetic(getModifiers());
    }
    
    public Class getType() {
        return type;
    }
    
    public Type getGenericType() {
        if (getGenericSignature() != null) return getGenericInfo().getGenericType(); else return getType();
    }
    
    public boolean equals(Object obj) {
        if (obj != null && obj instanceof Field) {
            Field other = (Field)(Field)obj;
            return (getDeclaringClass() == other.getDeclaringClass()) && (getName() == other.getName()) && (getType() == other.getType());
        }
        return false;
    }
    
    public int hashCode() {
        return getDeclaringClass().getName().hashCode() ^ getName().hashCode();
    }
    
    public String toString() {
        int mod = getModifiers();
        return (((mod == 0) ? "" : (Modifier.toString(mod) + " ")) + getTypeName(getType()) + " " + getTypeName(getDeclaringClass()) + "." + getName());
    }
    
    public String toGenericString() {
        int mod = getModifiers();
        Type fieldType = getGenericType();
        return (((mod == 0) ? "" : (Modifier.toString(mod) + " ")) + ((fieldType instanceof Class) ? getTypeName((Class)(Class)fieldType) : fieldType.toString()) + " " + getTypeName(getDeclaringClass()) + "." + getName());
    }
    
    public Object get(Object obj) throws IllegalArgumentException, IllegalAccessException {
        return getFieldAccessor(obj).get(obj);
    }
    
    public boolean getBoolean(Object obj) throws IllegalArgumentException, IllegalAccessException {
        return getFieldAccessor(obj).getBoolean(obj);
    }
    
    public byte getByte(Object obj) throws IllegalArgumentException, IllegalAccessException {
        return getFieldAccessor(obj).getByte(obj);
    }
    
    public char getChar(Object obj) throws IllegalArgumentException, IllegalAccessException {
        return getFieldAccessor(obj).getChar(obj);
    }
    
    public short getShort(Object obj) throws IllegalArgumentException, IllegalAccessException {
        return getFieldAccessor(obj).getShort(obj);
    }
    
    public int getInt(Object obj) throws IllegalArgumentException, IllegalAccessException {
        return getFieldAccessor(obj).getInt(obj);
    }
    
    public long getLong(Object obj) throws IllegalArgumentException, IllegalAccessException {
        return getFieldAccessor(obj).getLong(obj);
    }
    
    public float getFloat(Object obj) throws IllegalArgumentException, IllegalAccessException {
        return getFieldAccessor(obj).getFloat(obj);
    }
    
    public double getDouble(Object obj) throws IllegalArgumentException, IllegalAccessException {
        return getFieldAccessor(obj).getDouble(obj);
    }
    
    public void set(Object obj, Object value) throws IllegalArgumentException, IllegalAccessException {
        getFieldAccessor(obj).set(obj, value);
    }
    
    public void setBoolean(Object obj, boolean z) throws IllegalArgumentException, IllegalAccessException {
        getFieldAccessor(obj).setBoolean(obj, z);
    }
    
    public void setByte(Object obj, byte b) throws IllegalArgumentException, IllegalAccessException {
        getFieldAccessor(obj).setByte(obj, b);
    }
    
    public void setChar(Object obj, char c) throws IllegalArgumentException, IllegalAccessException {
        getFieldAccessor(obj).setChar(obj, c);
    }
    
    public void setShort(Object obj, short s) throws IllegalArgumentException, IllegalAccessException {
        getFieldAccessor(obj).setShort(obj, s);
    }
    
    public void setInt(Object obj, int i) throws IllegalArgumentException, IllegalAccessException {
        getFieldAccessor(obj).setInt(obj, i);
    }
    
    public void setLong(Object obj, long l) throws IllegalArgumentException, IllegalAccessException {
        getFieldAccessor(obj).setLong(obj, l);
    }
    
    public void setFloat(Object obj, float f) throws IllegalArgumentException, IllegalAccessException {
        getFieldAccessor(obj).setFloat(obj, f);
    }
    
    public void setDouble(Object obj, double d) throws IllegalArgumentException, IllegalAccessException {
        getFieldAccessor(obj).setDouble(obj, d);
    }
    
    private FieldAccessor getFieldAccessor(Object obj) throws IllegalAccessException {
        doSecurityCheck(obj);
        boolean ov = override;
        FieldAccessor a = (ov) ? overrideFieldAccessor : fieldAccessor;
        return (a != null) ? a : acquireFieldAccessor(ov);
    }
    
    private FieldAccessor acquireFieldAccessor(boolean overrideFinalCheck) {
        FieldAccessor tmp = null;
        if (root != null) tmp = root.getFieldAccessor(overrideFinalCheck);
        if (tmp != null) {
            if (overrideFinalCheck) overrideFieldAccessor = tmp; else fieldAccessor = tmp;
        } else {
            tmp = reflectionFactory.newFieldAccessor(this, overrideFinalCheck);
            setFieldAccessor(tmp, overrideFinalCheck);
        }
        return tmp;
    }
    
    private FieldAccessor getFieldAccessor(boolean overrideFinalCheck) {
        return (overrideFinalCheck) ? overrideFieldAccessor : fieldAccessor;
    }
    
    private void setFieldAccessor(FieldAccessor accessor, boolean overrideFinalCheck) {
        if (overrideFinalCheck) overrideFieldAccessor = accessor; else fieldAccessor = accessor;
        if (root != null) {
            root.setFieldAccessor(accessor, overrideFinalCheck);
        }
    }
    
    private void doSecurityCheck(Object obj) throws IllegalAccessException {
        if (!override) {
            if (!Reflection.quickCheckMemberAccess(clazz, modifiers)) {
                Class caller = Reflection.getCallerClass(4);
                Class targetClass = ((obj == null || !Modifier.isProtected(modifiers)) ? clazz : obj.getClass());
                if (securityCheckCache != caller || targetClass != securityCheckTargetClassCache) {
                    Reflection.ensureMemberAccess(caller, clazz, obj, modifiers);
                    securityCheckCache = caller;
                    securityCheckTargetClassCache = targetClass;
                }
            }
        }
    }
    
    static String getTypeName(Class type) {
        if (type.isArray()) {
            try {
                Class cl = type;
                int dimensions = 0;
                while (cl.isArray()) {
                    dimensions++;
                    cl = cl.getComponentType();
                }
                StringBuffer sb = new StringBuffer();
                sb.append(cl.getName());
                for (int i = 0; i < dimensions; i++) {
                    sb.append("[]");
                }
                return sb.toString();
            } catch (Throwable e) {
            }
        }
        return type.getName();
    }
    
    public Annotation getAnnotation(Class annotationClass) {
        if (annotationClass == null) throw new NullPointerException();
        return (Annotation)(Annotation)declaredAnnotations().get(annotationClass);
    }
    private static final Annotation[] EMPTY_ANNOTATION_ARRAY = new Annotation[0];
    
    public Annotation[] getDeclaredAnnotations() {
        return (Annotation[])declaredAnnotations().values().toArray(EMPTY_ANNOTATION_ARRAY);
    }
    private transient Map declaredAnnotations;
    
    private synchronized Map declaredAnnotations() {
        if (declaredAnnotations == null) {
            declaredAnnotations = AnnotationParser.parseAnnotations(annotations, sun.misc.SharedSecrets.getJavaLangAccess().getConstantPool(getDeclaringClass()), getDeclaringClass());
        }
        return declaredAnnotations;
    }
}
