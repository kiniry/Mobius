package java.beans;

import java.lang.ref.Reference;
import java.lang.reflect.Method;

public class EventSetDescriptor extends FeatureDescriptor {
    private MethodDescriptor[] listenerMethodDescriptors;
    private MethodDescriptor addMethodDescriptor;
    private MethodDescriptor removeMethodDescriptor;
    private MethodDescriptor getMethodDescriptor;
    private Reference listenerMethodsRef;
    private Reference listenerTypeRef;
    private boolean unicast;
    private boolean inDefaultEventSet = true;
    
    public EventSetDescriptor(Class sourceClass, String eventSetName, Class listenerType, String listenerMethodName) throws IntrospectionException {
        this(sourceClass, eventSetName, listenerType, new String[]{listenerMethodName}, "add" + getListenerClassName(listenerType), "remove" + getListenerClassName(listenerType), "get" + getListenerClassName(listenerType) + "s");
        String eventName = capitalize(eventSetName) + "Event";
        Method[] listenerMethods = getListenerMethods();
        if (listenerMethods.length > 0) {
            Class[] args = listenerMethods[0].getParameterTypes();
            if (!"vetoableChange".equals(eventSetName) && !args[0].getName().endsWith(eventName)) {
                throw new IntrospectionException("Method \"" + listenerMethodName + "\" should have argument \"" + eventName + "\"");
            }
        }
    }
    
    private static String getListenerClassName(Class cls) {
        String className = cls.getName();
        return className.substring(className.lastIndexOf('.') + 1);
    }
    
    public EventSetDescriptor(Class sourceClass, String eventSetName, Class listenerType, String[] listenerMethodNames, String addListenerMethodName, String removeListenerMethodName) throws IntrospectionException {
        this(sourceClass, eventSetName, listenerType, listenerMethodNames, addListenerMethodName, removeListenerMethodName, null);
    }
    
    public EventSetDescriptor(Class sourceClass, String eventSetName, Class listenerType, String[] listenerMethodNames, String addListenerMethodName, String removeListenerMethodName, String getListenerMethodName) throws IntrospectionException {
        
        if (sourceClass == null || eventSetName == null || listenerType == null) {
            throw new NullPointerException();
        }
        setName(eventSetName);
        setClass0(sourceClass);
        setListenerType(listenerType);
        Method[] listenerMethods = new Method[listenerMethodNames.length];
        for (int i = 0; i < listenerMethodNames.length; i++) {
            if (listenerMethodNames[i] == null) {
                throw new NullPointerException();
            }
            listenerMethods[i] = getMethod(listenerType, listenerMethodNames[i], 1);
        }
        setListenerMethods(listenerMethods);
        setAddListenerMethod(getMethod(sourceClass, addListenerMethodName, 1));
        setRemoveListenerMethod(getMethod(sourceClass, removeListenerMethodName, 1));
        Method method = Introspector.findMethod(sourceClass, getListenerMethodName, 0);
        if (method != null) {
            setGetListenerMethod(method);
        }
    }
    
    private static Method getMethod(Class cls, String name, int args) throws IntrospectionException {
        if (name == null) {
            return null;
        }
        Method method = Introspector.findMethod(cls, name, args);
        if (method == null) {
            throw new IntrospectionException("Method not found: " + name + " on class " + cls.getName());
        }
        return method;
    }
    
    public EventSetDescriptor(String eventSetName, Class listenerType, Method[] listenerMethods, Method addListenerMethod, Method removeListenerMethod) throws IntrospectionException {
        this(eventSetName, listenerType, listenerMethods, addListenerMethod, removeListenerMethod, null);
    }
    
    public EventSetDescriptor(String eventSetName, Class listenerType, Method[] listenerMethods, Method addListenerMethod, Method removeListenerMethod, Method getListenerMethod) throws IntrospectionException {
        
        setName(eventSetName);
        setListenerMethods(listenerMethods);
        setAddListenerMethod(addListenerMethod);
        setRemoveListenerMethod(removeListenerMethod);
        setGetListenerMethod(getListenerMethod);
        setListenerType(listenerType);
    }
    
    public EventSetDescriptor(String eventSetName, Class listenerType, MethodDescriptor[] listenerMethodDescriptors, Method addListenerMethod, Method removeListenerMethod) throws IntrospectionException {
        
        setName(eventSetName);
        this.listenerMethodDescriptors = listenerMethodDescriptors;
        setAddListenerMethod(addListenerMethod);
        setRemoveListenerMethod(removeListenerMethod);
        setListenerType(listenerType);
    }
    
    public Class getListenerType() {
        return (Class)(Class)getObject(listenerTypeRef);
    }
    
    private void setListenerType(Class cls) {
        listenerTypeRef = createReference(cls);
    }
    
    public synchronized Method[] getListenerMethods() {
        Method[] methods = getListenerMethods0();
        if (methods == null) {
            if (listenerMethodDescriptors != null) {
                methods = new Method[listenerMethodDescriptors.length];
                for (int i = 0; i < methods.length; i++) {
                    methods[i] = listenerMethodDescriptors[i].getMethod();
                }
            }
            setListenerMethods(methods);
        }
        return methods;
    }
    
    private void setListenerMethods(Method[] methods) {
        if (methods == null) {
            return;
        }
        if (listenerMethodDescriptors == null) {
            listenerMethodDescriptors = new MethodDescriptor[methods.length];
            for (int i = 0; i < methods.length; i++) {
                listenerMethodDescriptors[i] = new MethodDescriptor(methods[i]);
            }
        }
        listenerMethodsRef = createReference(methods, true);
    }
    
    private Method[] getListenerMethods0() {
        return (Method[])(Method[])getObject(listenerMethodsRef);
    }
    
    public synchronized MethodDescriptor[] getListenerMethodDescriptors() {
        return listenerMethodDescriptors;
    }
    
    public synchronized Method getAddListenerMethod() {
        return (addMethodDescriptor != null ? addMethodDescriptor.getMethod() : null);
    }
    
    private synchronized void setAddListenerMethod(Method method) {
        if (method == null) {
            return;
        }
        if (getClass0() == null) {
            setClass0(method.getDeclaringClass());
        }
        addMethodDescriptor = new MethodDescriptor(method);
    }
    
    public synchronized Method getRemoveListenerMethod() {
        return (removeMethodDescriptor != null ? removeMethodDescriptor.getMethod() : null);
    }
    
    private synchronized void setRemoveListenerMethod(Method method) {
        if (method == null) {
            return;
        }
        if (getClass0() == null) {
            setClass0(method.getDeclaringClass());
        }
        removeMethodDescriptor = new MethodDescriptor(method);
    }
    
    public synchronized Method getGetListenerMethod() {
        return (getMethodDescriptor != null ? getMethodDescriptor.getMethod() : null);
    }
    
    private synchronized void setGetListenerMethod(Method method) {
        if (method == null) {
            return;
        }
        if (getClass0() == null) {
            setClass0(method.getDeclaringClass());
        }
        getMethodDescriptor = new MethodDescriptor(method);
    }
    
    public void setUnicast(boolean unicast) {
        this.unicast = unicast;
    }
    
    public boolean isUnicast() {
        return unicast;
    }
    
    public void setInDefaultEventSet(boolean inDefaultEventSet) {
        this.inDefaultEventSet = inDefaultEventSet;
    }
    
    public boolean isInDefaultEventSet() {
        return inDefaultEventSet;
    }
    
    EventSetDescriptor(EventSetDescriptor x, EventSetDescriptor y) {
        super(x, y);
        listenerMethodDescriptors = x.listenerMethodDescriptors;
        if (y.listenerMethodDescriptors != null) {
            listenerMethodDescriptors = y.listenerMethodDescriptors;
        }
        listenerTypeRef = x.listenerTypeRef;
        if (y.listenerTypeRef != null) {
            listenerTypeRef = y.listenerTypeRef;
        }
        addMethodDescriptor = x.addMethodDescriptor;
        if (y.addMethodDescriptor != null) {
            addMethodDescriptor = y.addMethodDescriptor;
        }
        removeMethodDescriptor = x.removeMethodDescriptor;
        if (y.removeMethodDescriptor != null) {
            removeMethodDescriptor = y.removeMethodDescriptor;
        }
        getMethodDescriptor = x.getMethodDescriptor;
        if (y.getMethodDescriptor != null) {
            getMethodDescriptor = y.getMethodDescriptor;
        }
        unicast = y.unicast;
        if (!x.inDefaultEventSet || !y.inDefaultEventSet) {
            inDefaultEventSet = false;
        }
    }
    
    EventSetDescriptor(EventSetDescriptor old) {
        super(old);
        if (old.listenerMethodDescriptors != null) {
            int len = old.listenerMethodDescriptors.length;
            listenerMethodDescriptors = new MethodDescriptor[len];
            for (int i = 0; i < len; i++) {
                listenerMethodDescriptors[i] = new MethodDescriptor(old.listenerMethodDescriptors[i]);
            }
        }
        listenerTypeRef = old.listenerTypeRef;
        addMethodDescriptor = old.addMethodDescriptor;
        removeMethodDescriptor = old.removeMethodDescriptor;
        getMethodDescriptor = old.getMethodDescriptor;
        unicast = old.unicast;
        inDefaultEventSet = old.inDefaultEventSet;
    }
}
