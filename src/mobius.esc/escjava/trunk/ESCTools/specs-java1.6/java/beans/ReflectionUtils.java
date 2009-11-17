package java.beans;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.ref.Reference;
import java.lang.ref.SoftReference;
import java.util.*;
import com.sun.beans.ObjectHandler;
import sun.reflect.misc.MethodUtil;
import sun.reflect.misc.ConstructorUtil;
import sun.reflect.misc.ReflectUtil;

class ReflectionUtils {
    
    ReflectionUtils() {
        
    }
    private static Reference methodCacheRef;
    
    public static Class typeToClass(Class type) {
        return type.isPrimitive() ? ObjectHandler.typeNameToClass(type.getName()) : type;
    }
    
    public static boolean isPrimitive(Class type) {
        return primitiveTypeFor(type) != null;
    }
    
    public static Class primitiveTypeFor(Class wrapper) {
        if (wrapper == Boolean.class) return Boolean.TYPE;
        if (wrapper == Byte.class) return Byte.TYPE;
        if (wrapper == Character.class) return Character.TYPE;
        if (wrapper == Short.class) return Short.TYPE;
        if (wrapper == Integer.class) return Integer.TYPE;
        if (wrapper == Long.class) return Long.TYPE;
        if (wrapper == Float.class) return Float.TYPE;
        if (wrapper == Double.class) return Double.TYPE;
        if (wrapper == Void.class) return Void.TYPE;
        return null;
    }
    
    private static boolean matchArguments(Class[] argClasses, Class[] argTypes) {
        return matchArguments(argClasses, argTypes, false);
    }
    
    private static boolean matchExplicitArguments(Class[] argClasses, Class[] argTypes) {
        return matchArguments(argClasses, argTypes, true);
    }
    
    private static boolean matchArguments(Class[] argClasses, Class[] argTypes, boolean explicit) {
        boolean match = (argClasses.length == argTypes.length);
        for (int j = 0; j < argClasses.length && match; j++) {
            Class argType = argTypes[j];
            if (argType.isPrimitive()) {
                argType = typeToClass(argType);
            }
            if (explicit) {
                if (argClasses[j] != argType) {
                    match = false;
                }
            } else {
                if (argClasses[j] != null && !(argType.isAssignableFrom(argClasses[j]))) {
                    match = false;
                }
            }
        }
        return match;
    }
    
    static Method getPublicMethod(Class declaringClass, String methodName, Class[] argClasses) throws NoSuchMethodException {
        Method m;
        m = findPublicMethod(declaringClass, methodName, argClasses);
        if (m == null) throw new NoSuchMethodException(declaringClass.getName() + "." + methodName);
        return m;
    }
    
    public static Method findPublicMethod(Class declaringClass, String methodName, Class[] argClasses) {
        if (argClasses.length == 0) {
            try {
                return MethodUtil.getMethod(declaringClass, methodName, argClasses);
            } catch (NoSuchMethodException e) {
                return null;
            } catch (SecurityException se) {
            }
        }
        Method[] methods = MethodUtil.getPublicMethods(declaringClass);
        List list = new ArrayList();
        for (int i = 0; i < methods.length; i++) {
            Method method = methods[i];
            if (method.getName().equals(methodName)) {
                if (matchArguments(argClasses, method.getParameterTypes())) {
                    list.add(method);
                }
            }
        }
        if (list.size() > 0) {
            if (list.size() == 1) {
                return (Method)(Method)list.get(0);
            } else {
                ListIterator iterator = list.listIterator();
                Method method;
                while (iterator.hasNext()) {
                    method = (Method)(Method)iterator.next();
                    if (matchExplicitArguments(argClasses, method.getParameterTypes())) {
                        return method;
                    }
                }
                return getMostSpecificMethod(list, argClasses);
            }
        }
        return null;
    }
    
    private static Method getMostSpecificMethod(List methods, Class[] args) {
        Method method = null;
        int matches = 0;
        int lastMatch = matches;
        ListIterator iterator = methods.listIterator();
        while (iterator.hasNext()) {
            Method m = (Method)(Method)iterator.next();
            Class[] mArgs = m.getParameterTypes();
            matches = 0;
            for (int i = 0; i < args.length; i++) {
                Class mArg = mArgs[i];
                if (mArg.isPrimitive()) {
                    mArg = typeToClass(mArg);
                }
                if (args[i] == mArg) {
                    matches++;
                }
            }
            if (matches == 0 && lastMatch == 0) {
                if (method == null) {
                    method = m;
                } else {
                    if (!matchArguments(method.getParameterTypes(), m.getParameterTypes())) {
                        method = m;
                    }
                }
            } else if (matches > lastMatch) {
                lastMatch = matches;
                method = m;
            } else if (matches == lastMatch) {
                method = null;
            }
        }
        return method;
    }
    
    public static Method findMethod(Class targetClass, String methodName, Class[] argClasses) {
        Method m = findPublicMethod(targetClass, methodName, argClasses);
        if (m != null && Modifier.isPublic(m.getDeclaringClass().getModifiers())) {
            return m;
        }
        for (Class type = targetClass; type != null; type = type.getSuperclass()) {
            Class[] interfaces = type.getInterfaces();
            for (int i = 0; i < interfaces.length; i++) {
                m = findPublicMethod(interfaces[i], methodName, argClasses);
                if (m != null) {
                    return m;
                }
            }
        }
        return null;
    }
    {
    }
    
    public static synchronized Method getMethod(Class targetClass, String methodName, Class[] argClasses) {
        Object signature = new ReflectionUtils$Signature(targetClass, methodName, argClasses);
        Method method = null;
        Map methodCache = null;
        boolean cache = false;
        if (ReflectUtil.isPackageAccessible(targetClass)) {
            cache = true;
        }
        if (cache && methodCacheRef != null && (methodCache = (Map)(Map)methodCacheRef.get()) != null) {
            method = (Method)(Method)methodCache.get(signature);
            if (method != null) {
                return method;
            }
        }
        method = findMethod(targetClass, methodName, argClasses);
        if (cache && method != null) {
            if (methodCache == null) {
                methodCache = new HashMap();
                methodCacheRef = new SoftReference(methodCache);
            }
            methodCache.put(signature, method);
        }
        return method;
    }
    
    public static Constructor getConstructor(Class cls, Class[] args) {
        Constructor constructor = null;
        Constructor[] ctors = ConstructorUtil.getConstructors(cls);
        for (int i = 0; i < ctors.length; i++) {
            if (matchArguments(args, ctors[i].getParameterTypes())) {
                constructor = ctors[i];
            }
        }
        return constructor;
    }
    
    public static Object getPrivateField(Object instance, Class cls, String name) {
        return getPrivateField(instance, cls, name);
    }
    
    public static Object getPrivateField(Object instance, Class cls, String name, ExceptionListener el) {
        try {
            Field f = cls.getDeclaredField(name);
            f.setAccessible(true);
            return f.get(instance);
        } catch (Exception e) {
            if (el != null) {
                el.exceptionThrown(e);
            }
        }
        return null;
    }
}
