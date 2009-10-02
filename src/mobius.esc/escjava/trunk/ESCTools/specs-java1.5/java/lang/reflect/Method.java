package java.lang.reflect;

import sun.reflect.MethodAccessor;
import sun.reflect.Reflection;
import sun.reflect.generics.repository.MethodRepository;
import sun.reflect.generics.factory.CoreReflectionFactory;
import sun.reflect.generics.factory.GenericsFactory;
import sun.reflect.generics.scope.MethodScope;
import sun.reflect.annotation.AnnotationType;
import sun.reflect.annotation.AnnotationParser;
import java.lang.annotation.Annotation;
import java.lang.annotation.AnnotationFormatError;
import java.nio.ByteBuffer;
import java.util.Map;

public final class Method extends AccessibleObject implements GenericDeclaration, Member {
    private Class clazz;
    private int slot;
    private String name;
    private Class returnType;
    private Class[] parameterTypes;
    private Class[] exceptionTypes;
    private int modifiers;
    private transient String signature;
    private transient MethodRepository genericInfo;
    private byte[] annotations;
    private byte[] parameterAnnotations;
    private byte[] annotationDefault;
    private volatile MethodAccessor methodAccessor;
    private Method root;
    private volatile Class securityCheckTargetClassCache;
    
    private String getGenericSignature() {
        return signature;
    }
    
    private GenericsFactory getFactory() {
        return CoreReflectionFactory.make(this, MethodScope.make(this));
    }
    
    private MethodRepository getGenericInfo() {
        if (genericInfo == null) {
            genericInfo = MethodRepository.make(getGenericSignature(), getFactory());
        }
        return genericInfo;
    }
    
    Method(Class declaringClass, String name, Class[] parameterTypes, Class returnType, Class[] checkedExceptions, int modifiers, int slot, String signature, byte[] annotations, byte[] parameterAnnotations, byte[] annotationDefault) {
        
        this.clazz = declaringClass;
        this.name = name;
        this.parameterTypes = parameterTypes;
        this.returnType = returnType;
        this.exceptionTypes = checkedExceptions;
        this.modifiers = modifiers;
        this.slot = slot;
        this.signature = signature;
        this.annotations = annotations;
        this.parameterAnnotations = parameterAnnotations;
        this.annotationDefault = annotationDefault;
    }
    
    Method copy() {
        Method res = new Method(clazz, name, parameterTypes, returnType, exceptionTypes, modifiers, slot, signature, annotations, parameterAnnotations, annotationDefault);
        res.root = this;
        res.methodAccessor = methodAccessor;
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
    
    public TypeVariable[] getTypeParameters() {
        if (getGenericSignature() != null) return (TypeVariable[])getGenericInfo().getTypeParameters(); else return (TypeVariable[])new TypeVariable[0];
    }
    
    public Class getReturnType() {
        return returnType;
    }
    
    public Type getGenericReturnType() {
        if (getGenericSignature() != null) {
            return getGenericInfo().getReturnType();
        } else {
            return getReturnType();
        }
    }
    
    public Class[] getParameterTypes() {
        return (Class[])(Class[])parameterTypes.clone();
    }
    
    public Type[] getGenericParameterTypes() {
        if (getGenericSignature() != null) return getGenericInfo().getParameterTypes(); else return getParameterTypes();
    }
    
    public Class[] getExceptionTypes() {
        return (Class[])(Class[])exceptionTypes.clone();
    }
    
    public Type[] getGenericExceptionTypes() {
        Type[] result;
        if (getGenericSignature() != null && ((result = getGenericInfo().getExceptionTypes()).length > 0)) return result; else return getExceptionTypes();
    }
    
    public boolean equals(Object obj) {
        if (obj != null && obj instanceof Method) {
            Method other = (Method)(Method)obj;
            if ((getDeclaringClass() == other.getDeclaringClass()) && (getName() == other.getName())) {
                if (!returnType.equals(other.getReturnType())) return false;
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
        return getDeclaringClass().getName().hashCode() ^ getName().hashCode();
    }
    
    public String toString() {
        try {
            StringBuffer sb = new StringBuffer();
            int mod = getModifiers();
            if (mod != 0) {
                sb.append(Modifier.toString(mod) + " ");
            }
            sb.append(Field.getTypeName(getReturnType()) + " ");
            sb.append(Field.getTypeName(getDeclaringClass()) + ".");
            sb.append(getName() + "(");
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
            Type genRetType = getGenericReturnType();
            sb.append(((genRetType instanceof Class) ? Field.getTypeName((Class)(Class)genRetType) : genRetType.toString()) + " ");
            sb.append(Field.getTypeName(getDeclaringClass()) + ".");
            sb.append(getName() + "(");
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
    
    public Object invoke(Object obj, Object... args) throws IllegalAccessException, IllegalArgumentException, InvocationTargetException {
        if (!override) {
            if (!Reflection.quickCheckMemberAccess(clazz, modifiers)) {
                Class caller = Reflection.getCallerClass(1);
                Class targetClass = ((obj == null || !Modifier.isProtected(modifiers)) ? clazz : obj.getClass());
                if (securityCheckCache != caller || targetClass != securityCheckTargetClassCache) {
                    Reflection.ensureMemberAccess(caller, clazz, obj, modifiers);
                    securityCheckCache = caller;
                    securityCheckTargetClassCache = targetClass;
                }
            }
        }
        if (methodAccessor == null) acquireMethodAccessor();
        return methodAccessor.invoke(obj, args);
    }
    
    public boolean isBridge() {
        return (getModifiers() & Modifier.BRIDGE) != 0;
    }
    
    public boolean isVarArgs() {
        return (getModifiers() & Modifier.VARARGS) != 0;
    }
    
    public boolean isSynthetic() {
        return Modifier.isSynthetic(getModifiers());
    }
    
    private void acquireMethodAccessor() {
        MethodAccessor tmp = null;
        if (root != null) tmp = root.getMethodAccessor();
        if (tmp != null) {
            methodAccessor = tmp;
            return;
        }
        tmp = reflectionFactory.newMethodAccessor(this);
        setMethodAccessor(tmp);
    }
    
    MethodAccessor getMethodAccessor() {
        return methodAccessor;
    }
    
    void setMethodAccessor(MethodAccessor accessor) {
        methodAccessor = accessor;
        if (root != null) {
            root.setMethodAccessor(accessor);
        }
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
    
    public Object getDefaultValue() {
        if (annotationDefault == null) return null;
        Class memberType = AnnotationType.invocationHandlerReturnType(getReturnType());
        Object result = AnnotationParser.parseMemberValue(memberType, ByteBuffer.wrap(annotationDefault), sun.misc.SharedSecrets.getJavaLangAccess().getConstantPool(getDeclaringClass()), getDeclaringClass());
        if (result instanceof sun.reflect.annotation.ExceptionProxy) throw new AnnotationFormatError("Invalid default: " + this);
        return result;
    }
    
    public Annotation[][] getParameterAnnotations() {
        int numParameters = parameterTypes.length;
        if (parameterAnnotations == null) return new Annotation[numParameters][0];
        Annotation[][] result = AnnotationParser.parseParameterAnnotations(parameterAnnotations, sun.misc.SharedSecrets.getJavaLangAccess().getConstantPool(getDeclaringClass()), getDeclaringClass());
        if (result.length != numParameters) throw new java.lang.annotation.AnnotationFormatError("Parameter annotations don\'t match number of parameters");
        return result;
    }
}
