package java.lang.reflect;

import sun.reflect.ConstructorAccessor;
import sun.reflect.Reflection;
import sun.reflect.generics.repository.ConstructorRepository;
import sun.reflect.generics.factory.CoreReflectionFactory;
import sun.reflect.generics.factory.GenericsFactory;
import sun.reflect.generics.scope.ConstructorScope;
import java.lang.annotation.Annotation;
import java.util.Map;
import sun.reflect.annotation.AnnotationParser;

public final class Constructor extends AccessibleObject implements GenericDeclaration, Member {
    private Class clazz;
    private int slot;
    private Class[] parameterTypes;
    private Class[] exceptionTypes;
    private int modifiers;
    private transient String signature;
    private transient ConstructorRepository genericInfo;
    private byte[] annotations;
    private byte[] parameterAnnotations;
    
    private GenericsFactory getFactory() {
        return CoreReflectionFactory.make(this, ConstructorScope.make(this));
    }
    
    private ConstructorRepository getGenericInfo() {
        if (genericInfo == null) {
            genericInfo = ConstructorRepository.make(getSignature(), getFactory());
        }
        return genericInfo;
    }
    private volatile ConstructorAccessor constructorAccessor;
    private Constructor root;
    
    Constructor(Class declaringClass, Class[] parameterTypes, Class[] checkedExceptions, int modifiers, int slot, String signature, byte[] annotations, byte[] parameterAnnotations) {
        
        this.clazz = declaringClass;
        this.parameterTypes = parameterTypes;
        this.exceptionTypes = checkedExceptions;
        this.modifiers = modifiers;
        this.slot = slot;
        this.signature = signature;
        this.annotations = annotations;
        this.parameterAnnotations = parameterAnnotations;
    }
    
    Constructor copy() {
        Constructor res = new Constructor(clazz, parameterTypes, exceptionTypes, modifiers, slot, signature, annotations, parameterAnnotations);
        res.root = this;
        res.constructorAccessor = constructorAccessor;
        return res;
    }
    
    public Class getDeclaringClass() {
        return clazz;
    }
    
    public String getName() {
        return getDeclaringClass().getName();
    }
    
    public int getModifiers() {
        return modifiers;
    }
    
    public TypeVariable[] getTypeParameters() {
        if (getSignature() != null) {
            return (TypeVariable[])getGenericInfo().getTypeParameters();
        } else return (TypeVariable[])new TypeVariable[0];
    }
    
    public Class[] getParameterTypes() {
        return (Class[])(Class[])parameterTypes.clone();
    }
    
    public Type[] getGenericParameterTypes() {
        if (getSignature() != null) return getGenericInfo().getParameterTypes(); else return getParameterTypes();
    }
    
    public Class[] getExceptionTypes() {
        return (Class[])(Class[])exceptionTypes.clone();
    }
    
    public Type[] getGenericExceptionTypes() {
        Type[] result;
        if (getSignature() != null && ((result = getGenericInfo().getExceptionTypes()).length > 0)) return result; else return getExceptionTypes();
    }
    
    public boolean equals(Object obj) {
        if (obj != null && obj instanceof Constructor) {
            Constructor other = (Constructor)(Constructor)obj;
            if (getDeclaringClass() == other.getDeclaringClass()) {
                Class[] params1 = parameterTypes;
                Class[] params2 = other.parameterTypes;
                if (params1.length == params2.length) {
                    for (int i = 0; i < params1.length; i++) {
                        if (params1[i] != params2[i]) return false;
                    }
                    return true;
                }
            }
        }
        return false;
    }
    
    public int hashCode() {
        return getDeclaringClass().getName().hashCode();
    }
    
    public String toString() {
        try {
            StringBuffer sb = new StringBuffer();
            int mod = getModifiers();
            if (mod != 0) {
                sb.append(Modifier.toString(mod) + " ");
            }
            sb.append(Field.getTypeName(getDeclaringClass()));
            sb.append("(");
            Class[] params = parameterTypes;
            for (int j = 0; j < params.length; j++) {
                sb.append(Field.getTypeName(params[j]));
                if (j < (params.length - 1)) sb.append(",");
            }
            sb.append(")");
            Class[] exceptions = exceptionTypes;
            if (exceptions.length > 0) {
                sb.append(" throws ");
                for (int k = 0; k < exceptions.length; k++) {
                    sb.append(exceptions[k].getName());
                    if (k < (exceptions.length - 1)) sb.append(",");
                }
            }
            return sb.toString();
        } catch (Exception e) {
            return "<" + e + ">";
        }
    }
    
    public String toGenericString() {
        try {
            StringBuilder sb = new StringBuilder();
            int mod = getModifiers();
            if (mod != 0) {
                sb.append(Modifier.toString(mod) + " ");
            }
            Type[] typeparms = getTypeParameters();
            if (typeparms.length > 0) {
                boolean first = true;
                sb.append("<");
                for (Type[] arr$ = typeparms, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
                    Type typeparm = arr$[i$];
                    {
                        if (!first) sb.append(",");
                        if (typeparm instanceof Class) sb.append(((Class)(Class)typeparm).getName()); else sb.append(typeparm.toString());
                        first = false;
                    }
                }
                sb.append("> ");
            }
            sb.append(Field.getTypeName(getDeclaringClass()));
            sb.append("(");
            Type[] params = getGenericParameterTypes();
            for (int j = 0; j < params.length; j++) {
                sb.append((params[j] instanceof Class) ? Field.getTypeName((Class)(Class)params[j]) : (params[j].toString()));
                if (j < (params.length - 1)) sb.append(",");
            }
            sb.append(")");
            Type[] exceptions = getGenericExceptionTypes();
            if (exceptions.length > 0) {
                sb.append(" throws ");
                for (int k = 0; k < exceptions.length; k++) {
                    sb.append((exceptions[k] instanceof Class) ? ((Class)(Class)exceptions[k]).getName() : exceptions[k].toString());
                    if (k < (exceptions.length - 1)) sb.append(",");
                }
            }
            return sb.toString();
        } catch (Exception e) {
            return "<" + e + ">";
        }
    }
    
    public Object newInstance(Object... initargs) throws InstantiationException, IllegalAccessException, IllegalArgumentException, InvocationTargetException {
        if (!override) {
            if (!Reflection.quickCheckMemberAccess(clazz, modifiers)) {
                Class caller = Reflection.getCallerClass(2);
                if (securityCheckCache != caller) {
                    Reflection.ensureMemberAccess(caller, clazz, null, modifiers);
                    securityCheckCache = caller;
                }
            }
        }
        if ((clazz.getModifiers() & Modifier.ENUM) != 0) throw new IllegalArgumentException("Cannot reflectively create enum objects");
        if (constructorAccessor == null) acquireConstructorAccessor();
        return (Object)constructorAccessor.newInstance(initargs);
    }
    
    public boolean isVarArgs() {
        return (getModifiers() & Modifier.VARARGS) != 0;
    }
    
    public boolean isSynthetic() {
        return Modifier.isSynthetic(getModifiers());
    }
    
    private void acquireConstructorAccessor() {
        ConstructorAccessor tmp = null;
        if (root != null) tmp = root.getConstructorAccessor();
        if (tmp != null) {
            constructorAccessor = tmp;
            return;
        }
        tmp = reflectionFactory.newConstructorAccessor(this);
        setConstructorAccessor(tmp);
    }
    
    ConstructorAccessor getConstructorAccessor() {
        return constructorAccessor;
    }
    
    void setConstructorAccessor(ConstructorAccessor accessor) {
        constructorAccessor = accessor;
        if (root != null) {
            root.setConstructorAccessor(accessor);
        }
    }
    
    int getSlot() {
        return slot;
    }
    
    String getSignature() {
        return signature;
    }
    
    byte[] getRawAnnotations() {
        return annotations;
    }
    
    byte[] getRawParameterAnnotations() {
        return parameterAnnotations;
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
    
    public Annotation[][] getParameterAnnotations() {
        int numParameters = parameterTypes.length;
        if (parameterAnnotations == null) return new Annotation[numParameters][0];
        Annotation[][] result = AnnotationParser.parseParameterAnnotations(parameterAnnotations, sun.misc.SharedSecrets.getJavaLangAccess().getConstantPool(getDeclaringClass()), getDeclaringClass());
        if (result.length != numParameters) throw new java.lang.annotation.AnnotationFormatError("Parameter annotations don\'t match number of parameters");
        return result;
    }
}
