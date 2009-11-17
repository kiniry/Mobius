package java.lang;

import java.lang.reflect.Array;
import java.lang.reflect.GenericArrayType;
import java.lang.reflect.Member;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Constructor;
import java.lang.reflect.Modifier;
import java.lang.reflect.Type;
import java.lang.reflect.TypeVariable;
import java.lang.reflect.InvocationTargetException;
import java.lang.ref.SoftReference;
import java.io.InputStream;
import java.io.ObjectStreamClass;
import java.io.ObjectStreamField;
import java.security.AccessController;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Map;
import java.util.HashMap;
import sun.misc.Unsafe;
import sun.reflect.ConstantPool;
import sun.reflect.Reflection;
import sun.reflect.ReflectionFactory;
import sun.reflect.generics.factory.CoreReflectionFactory;
import sun.reflect.generics.factory.GenericsFactory;
import sun.reflect.generics.repository.ClassRepository;
import sun.reflect.generics.repository.MethodRepository;
import sun.reflect.generics.repository.ConstructorRepository;
import sun.reflect.generics.scope.ClassScope;
import sun.security.util.SecurityConstants;
import java.lang.annotation.Annotation;
import sun.reflect.annotation.*;

public final class Class implements java.io.Serializable, java.lang.reflect.GenericDeclaration, java.lang.reflect.Type, java.lang.reflect.AnnotatedElement {
    
    /*synthetic*/ static boolean access$302(boolean x0) {
        return initted = x0;
    }
    
    /*synthetic*/ static boolean access$202(boolean x0) {
        return useCaches = x0;
    }
    
    /*synthetic*/ static boolean access$100(Object[] x0, Object[] x1) {
        return arrayContentsEq(x0, x1);
    }
    private static final int ANNOTATION = 8192;
    private static final int ENUM = 16384;
    private static final int SYNTHETIC = 4096;
    
    private static native void registerNatives();
    static {
        registerNatives();
    }
    
    private Class() {
        
    }
    
    public String toString() {
        return (isInterface() ? "interface " : (isPrimitive() ? "" : "class ")) + getName();
    }
    
    public static Class forName(String className) throws ClassNotFoundException {
        return forName0(className, true, ClassLoader.getCallerClassLoader());
    }
    
    public static Class forName(String name, boolean initialize, ClassLoader loader) throws ClassNotFoundException {
        if (loader == null) {
            SecurityManager sm = System.getSecurityManager();
            if (sm != null) {
                ClassLoader ccl = ClassLoader.getCallerClassLoader();
                if (ccl != null) {
                    sm.checkPermission(SecurityConstants.GET_CLASSLOADER_PERMISSION);
                }
            }
        }
        return forName0(name, initialize, loader);
    }
    
    private static native Class forName0(String name, boolean initialize, ClassLoader loader) throws ClassNotFoundException;
    
    public Object newInstance() throws InstantiationException, IllegalAccessException {
        if (System.getSecurityManager() != null) {
            checkMemberAccess(Member.PUBLIC, ClassLoader.getCallerClassLoader());
        }
        return newInstance0();
    }
    
    private Object newInstance0() throws InstantiationException, IllegalAccessException {
        if (cachedConstructor == null) {
            if (this == Class.class) {
                throw new IllegalAccessException("Can not call newInstance() on the Class for java.lang.Class");
            }
            try {
                Class[] empty = {};
                final Constructor c = getConstructor0(empty, Member.DECLARED);
                java.security.AccessController.doPrivileged(new Class$1(this, c));
                cachedConstructor = c;
            } catch (NoSuchMethodException e) {
                throw new InstantiationException(getName());
            }
        }
        Constructor tmpConstructor = cachedConstructor;
        int modifiers = tmpConstructor.getModifiers();
        if (!Reflection.quickCheckMemberAccess(this, modifiers)) {
            Class caller = Reflection.getCallerClass(3);
            if (newInstanceCallerCache != caller) {
                Reflection.ensureMemberAccess(caller, this, null, modifiers);
                newInstanceCallerCache = caller;
            }
        }
        try {
            return tmpConstructor.newInstance((Object[])null);
        } catch (InvocationTargetException e) {
            Unsafe.getUnsafe().throwException(e.getTargetException());
            return null;
        }
    }
    private volatile transient Constructor cachedConstructor;
    private volatile transient Class newInstanceCallerCache;
    
    public native boolean isInstance(Object obj);
    
    public native boolean isAssignableFrom(Class cls);
    
    public native boolean isInterface();
    
    public native boolean isArray();
    
    public native boolean isPrimitive();
    
    public boolean isAnnotation() {
        return (getModifiers() & ANNOTATION) != 0;
    }
    
    public boolean isSynthetic() {
        return (getModifiers() & SYNTHETIC) != 0;
    }
    
    public String getName() {
        if (name == null) name = getName0();
        return name;
    }
    private transient String name;
    
    private native String getName0();
    
    public ClassLoader getClassLoader() {
        ClassLoader cl = getClassLoader0();
        if (cl == null) return null;
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            ClassLoader ccl = ClassLoader.getCallerClassLoader();
            if (ccl != null && ccl != cl && !cl.isAncestor(ccl)) {
                sm.checkPermission(SecurityConstants.GET_CLASSLOADER_PERMISSION);
            }
        }
        return cl;
    }
    
    native ClassLoader getClassLoader0();
    
    public TypeVariable[] getTypeParameters() {
        if (getGenericSignature() != null) return (TypeVariable[])getGenericInfo().getTypeParameters(); else return (TypeVariable[])new TypeVariable[0];
    }
    
    public native Class getSuperclass();
    
    public Type getGenericSuperclass() {
        if (getGenericSignature() != null) {
            if (isInterface()) return null;
            return getGenericInfo().getSuperclass();
        } else return getSuperclass();
    }
    
    public Package getPackage() {
        return Package.getPackage(this);
    }
    
    public native Class[] getInterfaces();
    
    public Type[] getGenericInterfaces() {
        if (getGenericSignature() != null) return getGenericInfo().getSuperInterfaces(); else return getInterfaces();
    }
    
    public native Class getComponentType();
    
    public native int getModifiers();
    
    public native Object[] getSigners();
    
    native void setSigners(Object[] signers);
    
    public Method getEnclosingMethod() {
        Class$EnclosingMethodInfo enclosingInfo = getEnclosingMethodInfo();
        if (enclosingInfo == null) return null; else {
            if (!enclosingInfo.isMethod()) return null;
            MethodRepository typeInfo = MethodRepository.make(enclosingInfo.getDescriptor(), getFactory());
            Class returnType = toClass(typeInfo.getReturnType());
            Type[] parameterTypes = typeInfo.getParameterTypes();
            Class[] parameterClasses = new Class[parameterTypes.length];
            for (int i = 0; i < parameterClasses.length; i++) parameterClasses[i] = toClass(parameterTypes[i]);
            for (Method[] arr$ = enclosingInfo.getEnclosingClass().getDeclaredMethods(), len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
                Method m = arr$[i$];
                {
                    if (m.getName().equals(enclosingInfo.getName())) {
                        Class[] candidateParamClasses = m.getParameterTypes();
                        if (candidateParamClasses.length == parameterClasses.length) {
                            boolean matches = true;
                            for (int i = 0; i < candidateParamClasses.length; i++) {
                                if (!candidateParamClasses[i].equals(parameterClasses[i])) {
                                    matches = false;
                                    break;
                                }
                            }
                            if (matches) {
                                if (m.getReturnType().equals(returnType)) return m;
                            }
                        }
                    }
                }
            }
            throw new InternalError("Enclosing method not found");
        }
    }
    
    private native Object[] getEnclosingMethod0();
    
    private Class$EnclosingMethodInfo getEnclosingMethodInfo() {
        if (isPrimitive()) return null;
        Object[] enclosingInfo = getEnclosingMethod0();
        if (enclosingInfo == null) return null; else {
            return new Class$EnclosingMethodInfo(enclosingInfo, null);
        }
    }
    {
    }
    
    private static Class toClass(Type o) {
        if (o instanceof GenericArrayType) return Array.newInstance(toClass(((GenericArrayType)(GenericArrayType)o).getGenericComponentType()), 0).getClass();
        return (Class)(Class)o;
    }
    
    public Constructor getEnclosingConstructor() {
        Class$EnclosingMethodInfo enclosingInfo = getEnclosingMethodInfo();
        if (enclosingInfo == null) return null; else {
            if (!enclosingInfo.isConstructor()) return null;
            ConstructorRepository typeInfo = ConstructorRepository.make(enclosingInfo.getDescriptor(), getFactory());
            Type[] parameterTypes = typeInfo.getParameterTypes();
            Class[] parameterClasses = new Class[parameterTypes.length];
            for (int i = 0; i < parameterClasses.length; i++) parameterClasses[i] = toClass(parameterTypes[i]);
            for (Constructor[] arr$ = enclosingInfo.getEnclosingClass().getDeclaredConstructors(), len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
                Constructor c = arr$[i$];
                {
                    Class[] candidateParamClasses = c.getParameterTypes();
                    if (candidateParamClasses.length == parameterClasses.length) {
                        boolean matches = true;
                        for (int i = 0; i < candidateParamClasses.length; i++) {
                            if (!candidateParamClasses[i].equals(parameterClasses[i])) {
                                matches = false;
                                break;
                            }
                        }
                        if (matches) return c;
                    }
                }
            }
            throw new InternalError("Enclosing constructor not found");
        }
    }
    
    public native Class getDeclaringClass();
    
    public Class getEnclosingClass() {
        Class$EnclosingMethodInfo enclosingInfo = getEnclosingMethodInfo();
        if (enclosingInfo == null) {
            return getDeclaringClass();
        } else {
            Class enclosingClass = enclosingInfo.getEnclosingClass();
            if (enclosingClass == this || enclosingClass == null) throw new InternalError("Malformed enclosing method information"); else return enclosingClass;
        }
    }
    
    public String getSimpleName() {
        if (isArray()) return getComponentType().getSimpleName() + "[]";
        String simpleName = getSimpleBinaryName();
        if (simpleName == null) {
            simpleName = getName();
            return simpleName.substring(simpleName.lastIndexOf(".") + 1);
        }
        int length = simpleName.length();
        if (length < 1 || simpleName.charAt(0) != '$') throw new InternalError("Malformed class name");
        int index = 1;
        while (index < length && isAsciiDigit(simpleName.charAt(index))) index++;
        return simpleName.substring(index);
    }
    
    private static boolean isAsciiDigit(char c) {
        return '0' <= c && c <= '9';
    }
    
    public String getCanonicalName() {
        if (isArray()) {
            String canonicalName = getComponentType().getCanonicalName();
            if (canonicalName != null) return canonicalName + "[]"; else return null;
        }
        if (isLocalOrAnonymousClass()) return null;
        Class enclosingClass = getEnclosingClass();
        if (enclosingClass == null) {
            return getName();
        } else {
            String enclosingName = enclosingClass.getCanonicalName();
            if (enclosingName == null) return null;
            return enclosingName + "." + getSimpleName();
        }
    }
    
    public boolean isAnonymousClass() {
        return "".equals(getSimpleName());
    }
    
    public boolean isLocalClass() {
        return isLocalOrAnonymousClass() && !isAnonymousClass();
    }
    
    public boolean isMemberClass() {
        return getSimpleBinaryName() != null && !isLocalOrAnonymousClass();
    }
    
    private String getSimpleBinaryName() {
        Class enclosingClass = getEnclosingClass();
        if (enclosingClass == null) return null;
        try {
            return getName().substring(enclosingClass.getName().length());
        } catch (IndexOutOfBoundsException ex) {
            throw new InternalError("Malformed class name");
        }
    }
    
    private boolean isLocalOrAnonymousClass() {
        return getEnclosingMethodInfo() != null;
    }
    
    public Class[] getClasses() {
        checkMemberAccess(Member.PUBLIC, ClassLoader.getCallerClassLoader());
        Class[] result = (Class[])(Class[])java.security.AccessController.doPrivileged(new Class$2(this));
        return result;
    }
    
    public Field[] getFields() throws SecurityException {
        checkMemberAccess(Member.PUBLIC, ClassLoader.getCallerClassLoader());
        return copyFields(privateGetPublicFields(null));
    }
    
    public Method[] getMethods() throws SecurityException {
        checkMemberAccess(Member.PUBLIC, ClassLoader.getCallerClassLoader());
        return copyMethods(privateGetPublicMethods());
    }
    
    public Constructor[] getConstructors() throws SecurityException {
        checkMemberAccess(Member.PUBLIC, ClassLoader.getCallerClassLoader());
        return copyConstructors(privateGetDeclaredConstructors(true));
    }
    
    public Field getField(String name) throws NoSuchFieldException, SecurityException {
        checkMemberAccess(Member.PUBLIC, ClassLoader.getCallerClassLoader());
        Field field = getField0(name);
        if (field == null) {
            throw new NoSuchFieldException(name);
        }
        return field;
    }
    
    public Method getMethod(String name, Class[] parameterTypes) throws NoSuchMethodException, SecurityException {
        checkMemberAccess(Member.PUBLIC, ClassLoader.getCallerClassLoader());
        Method method = getMethod0(name, parameterTypes);
        if (method == null) {
            throw new NoSuchMethodException(getName() + "." + name + argumentTypesToString(parameterTypes));
        }
        return method;
    }
    
    public Constructor getConstructor(Class[] parameterTypes) throws NoSuchMethodException, SecurityException {
        checkMemberAccess(Member.PUBLIC, ClassLoader.getCallerClassLoader());
        return getConstructor0(parameterTypes, Member.PUBLIC);
    }
    
    public Class[] getDeclaredClasses() throws SecurityException {
        checkMemberAccess(Member.DECLARED, ClassLoader.getCallerClassLoader());
        return getDeclaredClasses0();
    }
    
    public Field[] getDeclaredFields() throws SecurityException {
        checkMemberAccess(Member.DECLARED, ClassLoader.getCallerClassLoader());
        return copyFields(privateGetDeclaredFields(false));
    }
    
    public Method[] getDeclaredMethods() throws SecurityException {
        checkMemberAccess(Member.DECLARED, ClassLoader.getCallerClassLoader());
        return copyMethods(privateGetDeclaredMethods(false));
    }
    
    public Constructor[] getDeclaredConstructors() throws SecurityException {
        checkMemberAccess(Member.DECLARED, ClassLoader.getCallerClassLoader());
        return copyConstructors(privateGetDeclaredConstructors(false));
    }
    
    public Field getDeclaredField(String name) throws NoSuchFieldException, SecurityException {
        checkMemberAccess(Member.DECLARED, ClassLoader.getCallerClassLoader());
        Field field = searchFields(privateGetDeclaredFields(false), name);
        if (field == null) {
            throw new NoSuchFieldException(name);
        }
        return field;
    }
    
    public Method getDeclaredMethod(String name, Class[] parameterTypes) throws NoSuchMethodException, SecurityException {
        checkMemberAccess(Member.DECLARED, ClassLoader.getCallerClassLoader());
        Method method = searchMethods(privateGetDeclaredMethods(false), name, parameterTypes);
        if (method == null) {
            throw new NoSuchMethodException(getName() + "." + name + argumentTypesToString(parameterTypes));
        }
        return method;
    }
    
    public Constructor getDeclaredConstructor(Class[] parameterTypes) throws NoSuchMethodException, SecurityException {
        checkMemberAccess(Member.DECLARED, ClassLoader.getCallerClassLoader());
        return getConstructor0(parameterTypes, Member.DECLARED);
    }
    
    public InputStream getResourceAsStream(String name) {
        name = resolveName(name);
        ClassLoader cl = getClassLoader0();
        if (cl == null) {
            return ClassLoader.getSystemResourceAsStream(name);
        }
        return cl.getResourceAsStream(name);
    }
    
    public java.net.URL getResource(String name) {
        name = resolveName(name);
        ClassLoader cl = getClassLoader0();
        if (cl == null) {
            return ClassLoader.getSystemResource(name);
        }
        return cl.getResource(name);
    }
    private static java.security.ProtectionDomain allPermDomain;
    
    public java.security.ProtectionDomain getProtectionDomain() {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(SecurityConstants.GET_PD_PERMISSION);
        }
        java.security.ProtectionDomain pd = getProtectionDomain0();
        if (pd == null) {
            if (allPermDomain == null) {
                java.security.Permissions perms = new java.security.Permissions();
                perms.add(SecurityConstants.ALL_PERMISSION);
                allPermDomain = new java.security.ProtectionDomain(null, perms);
            }
            pd = allPermDomain;
        }
        return pd;
    }
    
    private native java.security.ProtectionDomain getProtectionDomain0();
    
    native void setProtectionDomain0(java.security.ProtectionDomain pd);
    
    static native Class getPrimitiveClass(String name);
    
    private void checkMemberAccess(int which, ClassLoader ccl) {
        SecurityManager s = System.getSecurityManager();
        if (s != null) {
            s.checkMemberAccess(this, which);
            ClassLoader cl = getClassLoader0();
            if ((ccl != null) && (ccl != cl) && ((cl == null) || !cl.isAncestor(ccl))) {
                String name = this.getName();
                int i = name.lastIndexOf('.');
                if (i != -1) {
                    s.checkPackageAccess(name.substring(0, i));
                }
            }
        }
    }
    
    private String resolveName(String name) {
        if (name == null) {
            return name;
        }
        if (!name.startsWith("/")) {
            Class c = this;
            while (c.isArray()) {
                c = c.getComponentType();
            }
            String baseName = c.getName();
            int index = baseName.lastIndexOf('.');
            if (index != -1) {
                name = baseName.substring(0, index).replace('.', '/') + "/" + name;
            }
        } else {
            name = name.substring(1);
        }
        return name;
    }
    private static boolean useCaches = true;
    private volatile transient SoftReference declaredFields;
    private volatile transient SoftReference publicFields;
    private volatile transient SoftReference declaredMethods;
    private volatile transient SoftReference publicMethods;
    private volatile transient SoftReference declaredConstructors;
    private volatile transient SoftReference publicConstructors;
    private volatile transient SoftReference declaredPublicFields;
    private volatile transient SoftReference declaredPublicMethods;
    private volatile transient int classRedefinedCount = 0;
    private volatile transient int lastRedefinedCount = 0;
    
    private void clearCachesOnClassRedefinition() {
        if (lastRedefinedCount != classRedefinedCount) {
            declaredFields = publicFields = declaredPublicFields = null;
            declaredMethods = publicMethods = declaredPublicMethods = null;
            declaredConstructors = publicConstructors = null;
            annotations = declaredAnnotations = null;
            lastRedefinedCount = classRedefinedCount;
        }
    }
    
    private native String getGenericSignature();
    private transient ClassRepository genericInfo;
    
    private GenericsFactory getFactory() {
        return CoreReflectionFactory.make(this, ClassScope.make(this));
    }
    
    private ClassRepository getGenericInfo() {
        if (genericInfo == null) {
            genericInfo = ClassRepository.make(getGenericSignature(), getFactory());
        }
        return genericInfo;
    }
    
    private native byte[] getRawAnnotations();
    
    native ConstantPool getConstantPool();
    
    private Field[] privateGetDeclaredFields(boolean publicOnly) {
        checkInitted();
        Field[] res = null;
        if (useCaches) {
            clearCachesOnClassRedefinition();
            if (publicOnly) {
                if (declaredPublicFields != null) {
                    res = (Field[])(Field[])declaredPublicFields.get();
                }
            } else {
                if (declaredFields != null) {
                    res = (Field[])(Field[])declaredFields.get();
                }
            }
            if (res != null) return res;
        }
        res = Reflection.filterFields(this, getDeclaredFields0(publicOnly));
        if (useCaches) {
            if (publicOnly) {
                declaredPublicFields = new SoftReference(res);
            } else {
                declaredFields = new SoftReference(res);
            }
        }
        return res;
    }
    
    private Field[] privateGetPublicFields(Set traversedInterfaces) {
        checkInitted();
        Field[] res = null;
        if (useCaches) {
            clearCachesOnClassRedefinition();
            if (publicFields != null) {
                res = (Field[])(Field[])publicFields.get();
            }
            if (res != null) return res;
        }
        List fields = new ArrayList();
        if (traversedInterfaces == null) {
            traversedInterfaces = new HashSet();
        }
        Field[] tmp = privateGetDeclaredFields(true);
        addAll(fields, tmp);
        Class[] interfaces = getInterfaces();
        for (int i = 0; i < interfaces.length; i++) {
            Class c = interfaces[i];
            if (!traversedInterfaces.contains(c)) {
                traversedInterfaces.add(c);
                addAll(fields, c.privateGetPublicFields(traversedInterfaces));
            }
        }
        if (!isInterface()) {
            Class c = getSuperclass();
            if (c != null) {
                addAll(fields, c.privateGetPublicFields(traversedInterfaces));
            }
        }
        res = new Field[fields.size()];
        fields.toArray(res);
        if (useCaches) {
            publicFields = new SoftReference(res);
        }
        return res;
    }
    
    private static void addAll(Collection c, Field[] o) {
        for (int i = 0; i < o.length; i++) {
            c.add(o[i]);
        }
    }
    
    private Constructor[] privateGetDeclaredConstructors(boolean publicOnly) {
        checkInitted();
        Constructor[] res = null;
        if (useCaches) {
            clearCachesOnClassRedefinition();
            if (publicOnly) {
                if (publicConstructors != null) {
                    res = (Constructor[])(Constructor[])publicConstructors.get();
                }
            } else {
                if (declaredConstructors != null) {
                    res = (Constructor[])(Constructor[])declaredConstructors.get();
                }
            }
            if (res != null) return res;
        }
        if (isInterface()) {
            res = new Constructor[0];
        } else {
            res = getDeclaredConstructors0(publicOnly);
        }
        if (useCaches) {
            if (publicOnly) {
                publicConstructors = new SoftReference(res);
            } else {
                declaredConstructors = new SoftReference(res);
            }
        }
        return res;
    }
    
    private Method[] privateGetDeclaredMethods(boolean publicOnly) {
        checkInitted();
        Method[] res = null;
        if (useCaches) {
            clearCachesOnClassRedefinition();
            if (publicOnly) {
                if (declaredPublicMethods != null) {
                    res = (Method[])(Method[])declaredPublicMethods.get();
                }
            } else {
                if (declaredMethods != null) {
                    res = (Method[])(Method[])declaredMethods.get();
                }
            }
            if (res != null) return res;
        }
        res = getDeclaredMethods0(publicOnly);
        if (useCaches) {
            if (publicOnly) {
                declaredPublicMethods = new SoftReference(res);
            } else {
                declaredMethods = new SoftReference(res);
            }
        }
        return res;
    }
    {
    }
    
    private Method[] privateGetPublicMethods() {
        checkInitted();
        Method[] res = null;
        if (useCaches) {
            clearCachesOnClassRedefinition();
            if (publicMethods != null) {
                res = (Method[])(Method[])publicMethods.get();
            }
            if (res != null) return res;
        }
        Class$MethodArray methods = new Class$MethodArray();
        {
            Method[] tmp = privateGetDeclaredMethods(true);
            methods.addAll(tmp);
        }
        Class$MethodArray inheritedMethods = new Class$MethodArray();
        Class[] interfaces = getInterfaces();
        for (int i = 0; i < interfaces.length; i++) {
            inheritedMethods.addAll(interfaces[i].privateGetPublicMethods());
        }
        if (!isInterface()) {
            Class c = getSuperclass();
            if (c != null) {
                Class$MethodArray supers = new Class$MethodArray();
                supers.addAll(c.privateGetPublicMethods());
                for (int i = 0; i < supers.length(); i++) {
                    Method m = supers.get(i);
                    if (m != null && !Modifier.isAbstract(m.getModifiers())) {
                        inheritedMethods.removeByNameAndSignature(m);
                    }
                }
                supers.addAll(inheritedMethods);
                inheritedMethods = supers;
            }
        }
        for (int i = 0; i < methods.length(); i++) {
            Method m = methods.get(i);
            inheritedMethods.removeByNameAndSignature(m);
        }
        methods.addAllIfNotPresent(inheritedMethods);
        methods.compactAndTrim();
        res = methods.getArray();
        if (useCaches) {
            publicMethods = new SoftReference(res);
        }
        return res;
    }
    
    private Field searchFields(Field[] fields, String name) {
        String internedName = name.intern();
        for (int i = 0; i < fields.length; i++) {
            if (fields[i].getName() == internedName) {
                return getReflectionFactory().copyField(fields[i]);
            }
        }
        return null;
    }
    
    private Field getField0(String name) throws NoSuchFieldException {
        Field res = null;
        if ((res = searchFields(privateGetDeclaredFields(true), name)) != null) {
            return res;
        }
        Class[] interfaces = getInterfaces();
        for (int i = 0; i < interfaces.length; i++) {
            Class c = interfaces[i];
            if ((res = c.getField0(name)) != null) {
                return res;
            }
        }
        if (!isInterface()) {
            Class c = getSuperclass();
            if (c != null) {
                if ((res = c.getField0(name)) != null) {
                    return res;
                }
            }
        }
        return null;
    }
    
    private static Method searchMethods(Method[] methods, String name, Class[] parameterTypes) {
        Method res = null;
        String internedName = name.intern();
        for (int i = 0; i < methods.length; i++) {
            Method m = methods[i];
            if (m.getName() == internedName && arrayContentsEq(parameterTypes, m.getParameterTypes()) && (res == null || res.getReturnType().isAssignableFrom(m.getReturnType()))) res = m;
        }
        return (res == null ? res : getReflectionFactory().copyMethod(res));
    }
    
    private Method getMethod0(String name, Class[] parameterTypes) {
        Method res = null;
        if ((res = searchMethods(privateGetDeclaredMethods(true), name, parameterTypes)) != null) {
            return res;
        }
        if (!isInterface()) {
            Class c = getSuperclass();
            if (c != null) {
                if ((res = c.getMethod0(name, parameterTypes)) != null) {
                    return res;
                }
            }
        }
        Class[] interfaces = getInterfaces();
        for (int i = 0; i < interfaces.length; i++) {
            Class c = interfaces[i];
            if ((res = c.getMethod0(name, parameterTypes)) != null) {
                return res;
            }
        }
        return null;
    }
    
    private Constructor getConstructor0(Class[] parameterTypes, int which) throws NoSuchMethodException {
        Constructor[] constructors = privateGetDeclaredConstructors((which == Member.PUBLIC));
        for (int i = 0; i < constructors.length; i++) {
            if (arrayContentsEq(parameterTypes, constructors[i].getParameterTypes())) {
                return getReflectionFactory().copyConstructor(constructors[i]);
            }
        }
        throw new NoSuchMethodException(getName() + ".<init>" + argumentTypesToString(parameterTypes));
    }
    
    private static boolean arrayContentsEq(Object[] a1, Object[] a2) {
        if (a1 == null) {
            return a2 == null || a2.length == 0;
        }
        if (a2 == null) {
            return a1.length == 0;
        }
        if (a1.length != a2.length) {
            return false;
        }
        for (int i = 0; i < a1.length; i++) {
            if (a1[i] != a2[i]) {
                return false;
            }
        }
        return true;
    }
    
    private static Field[] copyFields(Field[] arg) {
        Field[] out = new Field[arg.length];
        ReflectionFactory fact = getReflectionFactory();
        for (int i = 0; i < arg.length; i++) {
            out[i] = fact.copyField(arg[i]);
        }
        return out;
    }
    
    private static Method[] copyMethods(Method[] arg) {
        Method[] out = new Method[arg.length];
        ReflectionFactory fact = getReflectionFactory();
        for (int i = 0; i < arg.length; i++) {
            out[i] = fact.copyMethod(arg[i]);
        }
        return out;
    }
    
    private static Constructor[] copyConstructors(Constructor[] arg) {
        Constructor[] out = new Constructor[arg.length];
        ReflectionFactory fact = getReflectionFactory();
        for (int i = 0; i < arg.length; i++) {
            out[i] = fact.copyConstructor(arg[i]);
        }
        return out;
    }
    
    private native Field[] getDeclaredFields0(boolean publicOnly);
    
    private native Method[] getDeclaredMethods0(boolean publicOnly);
    
    private native Constructor[] getDeclaredConstructors0(boolean publicOnly);
    
    private native Class[] getDeclaredClasses0();
    
    private static String argumentTypesToString(Class[] argTypes) {
        StringBuilder buf = new StringBuilder();
        buf.append("(");
        if (argTypes != null) {
            for (int i = 0; i < argTypes.length; i++) {
                if (i > 0) {
                    buf.append(", ");
                }
                Class c = argTypes[i];
                buf.append((c == null) ? "null" : c.getName());
            }
        }
        buf.append(")");
        return buf.toString();
    }
    private static final long serialVersionUID = 3206093459760846163L;
    private static final ObjectStreamField[] serialPersistentFields = ObjectStreamClass.NO_FIELDS;
    
    public boolean desiredAssertionStatus() {
        ClassLoader loader = getClassLoader();
        if (loader == null) return desiredAssertionStatus0(this);
        synchronized (loader) {
            return (loader.classAssertionStatus == null ? desiredAssertionStatus0(this) : loader.desiredAssertionStatus(getName()));
        }
    }
    
    private static native boolean desiredAssertionStatus0(Class clazz);
    
    public boolean isEnum() {
        return (this.getModifiers() & ENUM) != 0 && this.getSuperclass() == Enum.class;
    }
    
    private static ReflectionFactory getReflectionFactory() {
        if (reflectionFactory == null) {
            reflectionFactory = (ReflectionFactory)(ReflectionFactory)java.security.AccessController.doPrivileged(new sun.reflect.ReflectionFactory$GetReflectionFactoryAction());
        }
        return reflectionFactory;
    }
    private static ReflectionFactory reflectionFactory;
    private static boolean initted = false;
    
    private static void checkInitted() {
        if (initted) return;
        AccessController.doPrivileged(new Class$3());
    }
    
    public Object[] getEnumConstants() {
        if (enumConstants == null) {
            if (!isEnum()) return null;
            try {
                final Method values = getMethod("values", new Class[]{});
                java.security.AccessController.doPrivileged(new Class$4(this, values));
                enumConstants = (Object[])(Object[])values.invoke(null, new Object[]{});
            } catch (InvocationTargetException ex) {
                return null;
            } catch (NoSuchMethodException ex) {
                return null;
            } catch (IllegalAccessException ex) {
                return null;
            }
        }
        return (Object[])enumConstants.clone();
    }
    private volatile transient Object[] enumConstants = null;
    
    Map enumConstantDirectory() {
        if (enumConstantDirectory == null) {
            Object[] universe = getEnumConstants();
            if (universe == null) throw new IllegalArgumentException(getName() + " is not an enum type");
            Map m = new HashMap(2 * universe.length);
            for (Object[] arr$ = universe, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
                Object constant = arr$[i$];
                m.put(((Enum)(Enum)constant).name(), constant);
            }
            enumConstantDirectory = m;
        }
        return enumConstantDirectory;
    }
    private volatile transient Map enumConstantDirectory = null;
    
    public Object cast(Object obj) {
        if (obj != null && !isInstance(obj)) throw new ClassCastException();
        return (Object)obj;
    }
    
    public Class asSubclass(Class clazz) {
        if (clazz.isAssignableFrom(this)) return (Class)this; else throw new ClassCastException(this.toString());
    }
    
    public Annotation getAnnotation(Class annotationClass) {
        if (annotationClass == null) throw new NullPointerException();
        initAnnotationsIfNecessary();
        return (Annotation)(Annotation)annotations.get(annotationClass);
    }
    
    public boolean isAnnotationPresent(Class annotationClass) {
        if (annotationClass == null) throw new NullPointerException();
        return getAnnotation(annotationClass) != null;
    }
    private static Annotation[] EMPTY_ANNOTATIONS_ARRAY = new Annotation[0];
    
    public Annotation[] getAnnotations() {
        initAnnotationsIfNecessary();
        return (Annotation[])annotations.values().toArray(EMPTY_ANNOTATIONS_ARRAY);
    }
    
    public Annotation[] getDeclaredAnnotations() {
        initAnnotationsIfNecessary();
        return (Annotation[])declaredAnnotations.values().toArray(EMPTY_ANNOTATIONS_ARRAY);
    }
    private transient Map annotations;
    private transient Map declaredAnnotations;
    
    private synchronized void initAnnotationsIfNecessary() {
        clearCachesOnClassRedefinition();
        if (annotations != null) return;
        declaredAnnotations = AnnotationParser.parseAnnotations(getRawAnnotations(), getConstantPool(), this);
        Class superClass = getSuperclass();
        if (superClass == null) {
            annotations = declaredAnnotations;
        } else {
            annotations = new HashMap();
            superClass.initAnnotationsIfNecessary();
            for (Iterator i$ = superClass.annotations.entrySet().iterator(); i$.hasNext(); ) {
                Map$Entry e = (Map$Entry)i$.next();
                {
                    Class annotationClass = (Class)e.getKey();
                    if (AnnotationType.getInstance(annotationClass).isInherited()) annotations.put(annotationClass, e.getValue());
                }
            }
            annotations.putAll(declaredAnnotations);
        }
    }
    private AnnotationType annotationType;
    
    void setAnnotationType(AnnotationType type) {
        annotationType = type;
    }
    
    AnnotationType getAnnotationType() {
        return annotationType;
    }
}
