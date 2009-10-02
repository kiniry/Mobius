package java.beans;

import java.lang.ref.Reference;
import java.lang.ref.SoftReference;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.security.AccessController;
import java.util.Collections;
import java.util.Map;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.EventListener;
import java.util.List;
import java.util.WeakHashMap;
import java.util.TreeMap;
import sun.reflect.misc.ReflectUtil;

public class Introspector {
    public static final int USE_ALL_BEANINFO = 1;
    public static final int IGNORE_IMMEDIATE_BEANINFO = 2;
    public static final int IGNORE_ALL_BEANINFO = 3;
    private static Map declaredMethodCache = Collections.synchronizedMap(new WeakHashMap());
    private static Map beanInfoCache = Collections.synchronizedMap(new WeakHashMap());
    private Class beanClass;
    private BeanInfo explicitBeanInfo;
    private BeanInfo superBeanInfo;
    private BeanInfo[] additionalBeanInfo;
    private boolean propertyChangeSource = false;
    private static Class eventListenerType = EventListener.class;
    private String defaultEventName;
    private String defaultPropertyName;
    private int defaultEventIndex = -1;
    private int defaultPropertyIndex = -1;
    private Map methods;
    private Map properties;
    private Map events;
    private static final String DEFAULT_INFO_PATH = "sun.beans.infos";
    private static String[] searchPath = {DEFAULT_INFO_PATH};
    private static final EventSetDescriptor[] EMPTY_EVENTSETDESCRIPTORS = new EventSetDescriptor[0];
    private static final String ADD_PREFIX = "add";
    private static final String REMOVE_PREFIX = "remove";
    private static final String GET_PREFIX = "get";
    private static final String SET_PREFIX = "set";
    private static final String IS_PREFIX = "is";
    private static final String BEANINFO_SUFFIX = "BeanInfo";
    
    public static BeanInfo getBeanInfo(Class beanClass) throws IntrospectionException {
        if (!ReflectUtil.isPackageAccessible(beanClass)) {
            return (new Introspector(beanClass, null, USE_ALL_BEANINFO)).getBeanInfo();
        }
        BeanInfo bi = (BeanInfo)(BeanInfo)beanInfoCache.get(beanClass);
        if (bi == null) {
            bi = (new Introspector(beanClass, null, USE_ALL_BEANINFO)).getBeanInfo();
            beanInfoCache.put(beanClass, bi);
        }
        return bi;
    }
    
    public static BeanInfo getBeanInfo(Class beanClass, int flags) throws IntrospectionException {
        return getBeanInfo(beanClass, null, flags);
    }
    
    public static BeanInfo getBeanInfo(Class beanClass, Class stopClass) throws IntrospectionException {
        return getBeanInfo(beanClass, stopClass, USE_ALL_BEANINFO);
    }
    
    private static BeanInfo getBeanInfo(Class beanClass, Class stopClass, int flags) throws IntrospectionException {
        BeanInfo bi;
        if (stopClass == null && flags == USE_ALL_BEANINFO) {
            bi = getBeanInfo(beanClass);
        } else {
            bi = (new Introspector(beanClass, stopClass, flags)).getBeanInfo();
        }
        return bi;
    }
    
    public static String decapitalize(String name) {
        if (name == null || name.length() == 0) {
            return name;
        }
        if (name.length() > 1 && Character.isUpperCase(name.charAt(1)) && Character.isUpperCase(name.charAt(0))) {
            return name;
        }
        char[] chars = name.toCharArray();
        chars[0] = Character.toLowerCase(chars[0]);
        return new String(chars);
    }
    
    public static synchronized String[] getBeanInfoSearchPath() {
        String[] result = new String[searchPath.length];
        for (int i = 0; i < searchPath.length; i++) {
            result[i] = searchPath[i];
        }
        return result;
    }
    
    public static synchronized void setBeanInfoSearchPath(String[] path) {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPropertiesAccess();
        }
        searchPath = path;
    }
    
    public static void flushCaches() {
        beanInfoCache.clear();
        declaredMethodCache.clear();
    }
    
    public static void flushFromCaches(Class clz) {
        if (clz == null) {
            throw new NullPointerException();
        }
        beanInfoCache.remove(clz);
        declaredMethodCache.remove(clz);
    }
    
    private Introspector(Class beanClass, Class stopClass, int flags) throws IntrospectionException {
        
        this.beanClass = beanClass;
        if (stopClass != null) {
            boolean isSuper = false;
            for (Class c = beanClass.getSuperclass(); c != null; c = c.getSuperclass()) {
                if (c == stopClass) {
                    isSuper = true;
                }
            }
            if (!isSuper) {
                throw new IntrospectionException(stopClass.getName() + " not superclass of " + beanClass.getName());
            }
        }
        if (flags == USE_ALL_BEANINFO) {
            explicitBeanInfo = findExplicitBeanInfo(beanClass);
        }
        Class superClass = beanClass.getSuperclass();
        if (superClass != stopClass) {
            int newFlags = flags;
            if (newFlags == IGNORE_IMMEDIATE_BEANINFO) {
                newFlags = USE_ALL_BEANINFO;
            }
            superBeanInfo = getBeanInfo(superClass, stopClass, newFlags);
        }
        if (explicitBeanInfo != null) {
            additionalBeanInfo = explicitBeanInfo.getAdditionalBeanInfo();
        }
        if (additionalBeanInfo == null) {
            additionalBeanInfo = new BeanInfo[0];
        }
    }
    
    private BeanInfo getBeanInfo() throws IntrospectionException {
        BeanDescriptor bd = getTargetBeanDescriptor();
        MethodDescriptor[] mds = getTargetMethodInfo();
        EventSetDescriptor[] esds = getTargetEventInfo();
        PropertyDescriptor[] pds = getTargetPropertyInfo();
        int defaultEvent = getTargetDefaultEventIndex();
        int defaultProperty = getTargetDefaultPropertyIndex();
        return new GenericBeanInfo(bd, esds, defaultEvent, pds, defaultProperty, mds, explicitBeanInfo);
    }
    
    private static synchronized BeanInfo findExplicitBeanInfo(Class beanClass) {
        String name = beanClass.getName() + BEANINFO_SUFFIX;
        try {
            return (java.beans.BeanInfo)(BeanInfo)instantiate(beanClass, name);
        } catch (Exception ex) {
        }
        try {
            if (isSubclass(beanClass, BeanInfo.class)) {
                return (java.beans.BeanInfo)(BeanInfo)beanClass.newInstance();
            }
        } catch (Exception ex) {
        }
        name = name.substring(name.lastIndexOf('.') + 1);
        for (int i = 0; i < searchPath.length; i++) {
            if (!DEFAULT_INFO_PATH.equals(searchPath[i]) || DEFAULT_INFO_PATH.equals(searchPath[i]) && "ComponentBeanInfo".equals(name)) {
                try {
                    String fullName = searchPath[i] + "." + name;
                    java.beans.BeanInfo bi = (java.beans.BeanInfo)(BeanInfo)instantiate(beanClass, fullName);
                    if (bi.getBeanDescriptor() != null) {
                        if (bi.getBeanDescriptor().getBeanClass() == beanClass) {
                            return bi;
                        }
                    } else if (bi.getPropertyDescriptors() != null) {
                        PropertyDescriptor[] pds = bi.getPropertyDescriptors();
                        for (int j = 0; j < pds.length; j++) {
                            Method method = pds[j].getReadMethod();
                            if (method == null) {
                                method = pds[j].getWriteMethod();
                            }
                            if (method != null && method.getDeclaringClass() == beanClass) {
                                return bi;
                            }
                        }
                    } else if (bi.getMethodDescriptors() != null) {
                        MethodDescriptor[] mds = bi.getMethodDescriptors();
                        for (int j = 0; j < mds.length; j++) {
                            Method method = mds[j].getMethod();
                            if (method != null && method.getDeclaringClass() == beanClass) {
                                return bi;
                            }
                        }
                    }
                } catch (Exception ex) {
                }
            }
        }
        return null;
    }
    
    private PropertyDescriptor[] getTargetPropertyInfo() {
        PropertyDescriptor[] explicitProperties = null;
        if (explicitBeanInfo != null) {
            explicitProperties = explicitBeanInfo.getPropertyDescriptors();
            int ix = explicitBeanInfo.getDefaultPropertyIndex();
            if (ix >= 0 && ix < explicitProperties.length) {
                defaultPropertyName = explicitProperties[ix].getName();
            }
        }
        if (explicitProperties == null && superBeanInfo != null) {
            PropertyDescriptor[] supers = superBeanInfo.getPropertyDescriptors();
            for (int i = 0; i < supers.length; i++) {
                addPropertyDescriptor(supers[i]);
            }
            int ix = superBeanInfo.getDefaultPropertyIndex();
            if (ix >= 0 && ix < supers.length) {
                defaultPropertyName = supers[ix].getName();
            }
        }
        for (int i = 0; i < additionalBeanInfo.length; i++) {
            PropertyDescriptor[] additional = additionalBeanInfo[i].getPropertyDescriptors();
            if (additional != null) {
                for (int j = 0; j < additional.length; j++) {
                    addPropertyDescriptor(additional[j]);
                }
            }
        }
        if (explicitProperties != null) {
            for (int i = 0; i < explicitProperties.length; i++) {
                addPropertyDescriptor(explicitProperties[i]);
            }
        } else {
            Method[] methodList = getPublicDeclaredMethods(beanClass);
            for (int i = 0; i < methodList.length; i++) {
                Method method = methodList[i];
                if (method == null) {
                    continue;
                }
                int mods = method.getModifiers();
                if (Modifier.isStatic(mods)) {
                    continue;
                }
                String name = method.getName();
                Class[] argTypes = method.getParameterTypes();
                Class resultType = method.getReturnType();
                int argCount = argTypes.length;
                PropertyDescriptor pd = null;
                if (name.length() <= 3 && !name.startsWith(IS_PREFIX)) {
                    continue;
                }
                try {
                    if (argCount == 0) {
                        if (name.startsWith(GET_PREFIX)) {
                            pd = new PropertyDescriptor(decapitalize(name.substring(3)), method, null);
                        } else if (resultType == Boolean.TYPE && name.startsWith(IS_PREFIX)) {
                            pd = new PropertyDescriptor(decapitalize(name.substring(2)), method, null);
                        }
                    } else if (argCount == 1) {
                        if (argTypes[0] == Integer.TYPE && name.startsWith(GET_PREFIX)) {
                            pd = new IndexedPropertyDescriptor(decapitalize(name.substring(3)), null, null, method, null);
                        } else if (resultType == Void.TYPE && name.startsWith(SET_PREFIX)) {
                            pd = new PropertyDescriptor(decapitalize(name.substring(3)), null, method);
                            if (throwsException(method, PropertyVetoException.class)) {
                                pd.setConstrained(true);
                            }
                        }
                    } else if (argCount == 2) {
                        if (argTypes[0] == Integer.TYPE && name.startsWith(SET_PREFIX)) {
                            pd = new IndexedPropertyDescriptor(decapitalize(name.substring(3)), null, null, null, method);
                            if (throwsException(method, PropertyVetoException.class)) {
                                pd.setConstrained(true);
                            }
                        }
                    }
                } catch (IntrospectionException ex) {
                    pd = null;
                }
                if (pd != null) {
                    if (propertyChangeSource) {
                        pd.setBound(true);
                    }
                    addPropertyDescriptor(pd);
                }
            }
        }
        processPropertyDescriptors();
        PropertyDescriptor[] result = new PropertyDescriptor[properties.size()];
        result = (PropertyDescriptor[])(PropertyDescriptor[])properties.values().toArray(result);
        if (defaultPropertyName != null) {
            for (int i = 0; i < result.length; i++) {
                if (defaultPropertyName.equals(result[i].getName())) {
                    defaultPropertyIndex = i;
                }
            }
        }
        return result;
    }
    private HashMap pdStore = new HashMap();
    
    private void addPropertyDescriptor(PropertyDescriptor pd) {
        String propName = pd.getName();
        List list = (List)(List)pdStore.get(propName);
        if (list == null) {
            list = new ArrayList();
            pdStore.put(propName, list);
        }
        list.add(pd);
    }
    
    private void processPropertyDescriptors() {
        if (properties == null) {
            properties = new TreeMap();
        }
        List list;
        PropertyDescriptor pd;
        PropertyDescriptor gpd;
        PropertyDescriptor spd;
        IndexedPropertyDescriptor ipd;
        IndexedPropertyDescriptor igpd;
        IndexedPropertyDescriptor ispd;
        Iterator it = pdStore.values().iterator();
        while (it.hasNext()) {
            pd = null;
            gpd = null;
            spd = null;
            ipd = null;
            igpd = null;
            ispd = null;
            list = (List)(List)it.next();
            for (int i = 0; i < list.size(); i++) {
                pd = (PropertyDescriptor)(PropertyDescriptor)list.get(i);
                if (pd instanceof IndexedPropertyDescriptor) {
                    ipd = (IndexedPropertyDescriptor)(IndexedPropertyDescriptor)pd;
                    if (ipd.getIndexedReadMethod() != null) {
                        if (igpd != null) {
                            igpd = new IndexedPropertyDescriptor(igpd, ipd);
                        } else {
                            igpd = ipd;
                        }
                    }
                } else {
                    if (pd.getReadMethod() != null) {
                        if (gpd != null) {
                            Method method = gpd.getReadMethod();
                            if (!method.getName().startsWith(IS_PREFIX)) {
                                gpd = new PropertyDescriptor(gpd, pd);
                            }
                        } else {
                            gpd = pd;
                        }
                    }
                }
            }
            for (int i = 0; i < list.size(); i++) {
                pd = (PropertyDescriptor)(PropertyDescriptor)list.get(i);
                if (pd instanceof IndexedPropertyDescriptor) {
                    ipd = (IndexedPropertyDescriptor)(IndexedPropertyDescriptor)pd;
                    if (ipd.getIndexedWriteMethod() != null) {
                        if (igpd != null) {
                            if (igpd.getIndexedPropertyType() == ipd.getIndexedPropertyType()) {
                                if (ispd != null) {
                                    ispd = new IndexedPropertyDescriptor(ispd, ipd);
                                } else {
                                    ispd = ipd;
                                }
                            }
                        } else {
                            if (ispd != null) {
                                ispd = new IndexedPropertyDescriptor(ispd, ipd);
                            } else {
                                ispd = ipd;
                            }
                        }
                    }
                } else {
                    if (pd.getWriteMethod() != null) {
                        if (gpd != null) {
                            if (gpd.getPropertyType() == pd.getPropertyType()) {
                                if (spd != null) {
                                    spd = new PropertyDescriptor(spd, pd);
                                } else {
                                    spd = pd;
                                }
                            }
                        } else {
                            if (spd != null) {
                                spd = new PropertyDescriptor(spd, pd);
                            } else {
                                spd = pd;
                            }
                        }
                    }
                }
            }
            pd = null;
            ipd = null;
            if (igpd != null && ispd != null) {
                if (gpd != null) {
                    PropertyDescriptor tpd = mergePropertyDescriptor(igpd, gpd);
                    if (tpd instanceof IndexedPropertyDescriptor) {
                        igpd = (IndexedPropertyDescriptor)(IndexedPropertyDescriptor)tpd;
                    }
                }
                if (spd != null) {
                    PropertyDescriptor tpd = mergePropertyDescriptor(ispd, spd);
                    if (tpd instanceof IndexedPropertyDescriptor) {
                        ispd = (IndexedPropertyDescriptor)(IndexedPropertyDescriptor)tpd;
                    }
                }
                if (igpd == ispd) {
                    pd = igpd;
                } else {
                    pd = mergePropertyDescriptor(igpd, ispd);
                }
            } else if (gpd != null && spd != null) {
                if (gpd == spd) {
                    pd = gpd;
                } else {
                    pd = mergePropertyDescriptor(gpd, spd);
                }
            } else if (ispd != null) {
                pd = ispd;
                if (spd != null) {
                    pd = mergePropertyDescriptor(ispd, spd);
                }
                if (gpd != null) {
                    pd = mergePropertyDescriptor(ispd, gpd);
                }
            } else if (igpd != null) {
                pd = igpd;
                if (gpd != null) {
                    pd = mergePropertyDescriptor(igpd, gpd);
                }
                if (spd != null) {
                    pd = mergePropertyDescriptor(igpd, spd);
                }
            } else if (spd != null) {
                pd = spd;
            } else if (gpd != null) {
                pd = gpd;
            }
            if (pd instanceof IndexedPropertyDescriptor) {
                ipd = (IndexedPropertyDescriptor)(IndexedPropertyDescriptor)pd;
                if (ipd.getIndexedReadMethod() == null && ipd.getIndexedWriteMethod() == null) {
                    pd = new PropertyDescriptor(ipd);
                }
            }
            if (pd != null) {
                properties.put(pd.getName(), pd);
            }
        }
    }
    
    private PropertyDescriptor mergePropertyDescriptor(IndexedPropertyDescriptor ipd, PropertyDescriptor pd) {
        PropertyDescriptor result = null;
        Class propType = pd.getPropertyType();
        Class ipropType = ipd.getIndexedPropertyType();
        if (propType.isArray() && propType.getComponentType() == ipropType) {
            if (pd.getClass0().isAssignableFrom(ipd.getClass0())) {
                result = new IndexedPropertyDescriptor(pd, ipd);
            } else {
                result = new IndexedPropertyDescriptor(ipd, pd);
            }
        } else {
            if (pd.getClass0().isAssignableFrom(ipd.getClass0())) {
                result = ipd;
            } else {
                result = pd;
                Method write = result.getWriteMethod();
                Method read = result.getReadMethod();
                if (read == null && write != null) {
                    read = findMethod(result.getClass0(), "get" + result.capitalize(result.getName()), 0);
                    if (read != null) {
                        try {
                            result.setReadMethod(read);
                        } catch (IntrospectionException ex) {
                        }
                    }
                }
                if (write == null && read != null) {
                    write = findMethod(result.getClass0(), "set" + result.capitalize(result.getName()), 1, new Class[]{read.getReturnType()});
                    if (write != null) {
                        try {
                            result.setWriteMethod(write);
                        } catch (IntrospectionException ex) {
                        }
                    }
                }
            }
        }
        return result;
    }
    
    private PropertyDescriptor mergePropertyDescriptor(PropertyDescriptor pd1, PropertyDescriptor pd2) {
        if (pd1.getClass0().isAssignableFrom(pd2.getClass0())) {
            return new PropertyDescriptor(pd1, pd2);
        } else {
            return new PropertyDescriptor(pd2, pd1);
        }
    }
    
    private PropertyDescriptor mergePropertyDescriptor(IndexedPropertyDescriptor ipd1, IndexedPropertyDescriptor ipd2) {
        if (ipd1.getClass0().isAssignableFrom(ipd2.getClass0())) {
            return new IndexedPropertyDescriptor(ipd1, ipd2);
        } else {
            return new IndexedPropertyDescriptor(ipd2, ipd1);
        }
    }
    
    private EventSetDescriptor[] getTargetEventInfo() throws IntrospectionException {
        if (events == null) {
            events = new HashMap();
        }
        EventSetDescriptor[] explicitEvents = null;
        if (explicitBeanInfo != null) {
            explicitEvents = explicitBeanInfo.getEventSetDescriptors();
            int ix = explicitBeanInfo.getDefaultEventIndex();
            if (ix >= 0 && ix < explicitEvents.length) {
                defaultEventName = explicitEvents[ix].getName();
            }
        }
        if (explicitEvents == null && superBeanInfo != null) {
            EventSetDescriptor[] supers = superBeanInfo.getEventSetDescriptors();
            for (int i = 0; i < supers.length; i++) {
                addEvent(supers[i]);
            }
            int ix = superBeanInfo.getDefaultEventIndex();
            if (ix >= 0 && ix < supers.length) {
                defaultEventName = supers[ix].getName();
            }
        }
        for (int i = 0; i < additionalBeanInfo.length; i++) {
            EventSetDescriptor[] additional = additionalBeanInfo[i].getEventSetDescriptors();
            if (additional != null) {
                for (int j = 0; j < additional.length; j++) {
                    addEvent(additional[j]);
                }
            }
        }
        if (explicitEvents != null) {
            for (int i = 0; i < explicitEvents.length; i++) {
                addEvent(explicitEvents[i]);
            }
        } else {
            Method[] methodList = getPublicDeclaredMethods(beanClass);
            Map adds = null;
            Map removes = null;
            Map gets = null;
            for (int i = 0; i < methodList.length; i++) {
                Method method = methodList[i];
                if (method == null) {
                    continue;
                }
                int mods = method.getModifiers();
                if (Modifier.isStatic(mods)) {
                    continue;
                }
                String name = method.getName();
                if (!name.startsWith(ADD_PREFIX) && !name.startsWith(REMOVE_PREFIX) && !name.startsWith(GET_PREFIX)) {
                    continue;
                }
                Class[] argTypes = method.getParameterTypes();
                Class resultType = method.getReturnType();
                if (name.startsWith(ADD_PREFIX) && argTypes.length == 1 && resultType == Void.TYPE && Introspector.isSubclass(argTypes[0], eventListenerType)) {
                    String listenerName = name.substring(3);
                    if (listenerName.length() > 0 && argTypes[0].getName().endsWith(listenerName)) {
                        if (adds == null) {
                            adds = new HashMap();
                        }
                        adds.put(listenerName, method);
                    }
                } else if (name.startsWith(REMOVE_PREFIX) && argTypes.length == 1 && resultType == Void.TYPE && Introspector.isSubclass(argTypes[0], eventListenerType)) {
                    String listenerName = name.substring(6);
                    if (listenerName.length() > 0 && argTypes[0].getName().endsWith(listenerName)) {
                        if (removes == null) {
                            removes = new HashMap();
                        }
                        removes.put(listenerName, method);
                    }
                } else if (name.startsWith(GET_PREFIX) && argTypes.length == 0 && resultType.isArray() && Introspector.isSubclass(resultType.getComponentType(), eventListenerType)) {
                    String listenerName = name.substring(3, name.length() - 1);
                    if (listenerName.length() > 0 && resultType.getComponentType().getName().endsWith(listenerName)) {
                        if (gets == null) {
                            gets = new HashMap();
                        }
                        gets.put(listenerName, method);
                    }
                }
            }
            if (adds != null && removes != null) {
                Iterator keys = adds.keySet().iterator();
                while (keys.hasNext()) {
                    String listenerName = (String)(String)keys.next();
                    if (removes.get(listenerName) == null || !listenerName.endsWith("Listener")) {
                        continue;
                    }
                    String eventName = decapitalize(listenerName.substring(0, listenerName.length() - 8));
                    Method addMethod = (Method)(Method)adds.get(listenerName);
                    Method removeMethod = (Method)(Method)removes.get(listenerName);
                    Method getMethod = null;
                    if (gets != null) {
                        getMethod = (Method)(Method)gets.get(listenerName);
                    }
                    Class argType = addMethod.getParameterTypes()[0];
                    Method[] allMethods = getPublicDeclaredMethods(argType);
                    List validMethods = new ArrayList(allMethods.length);
                    for (int i = 0; i < allMethods.length; i++) {
                        if (allMethods[i] == null) {
                            continue;
                        }
                        if (isEventHandler(allMethods[i])) {
                            validMethods.add(allMethods[i]);
                        }
                    }
                    Method[] methods = (Method[])(Method[])validMethods.toArray(new Method[validMethods.size()]);
                    EventSetDescriptor esd = new EventSetDescriptor(eventName, argType, methods, addMethod, removeMethod, getMethod);
                    if (throwsException(addMethod, .java.util.TooManyListenersException.class)) {
                        esd.setUnicast(true);
                    }
                    addEvent(esd);
                }
            }
        }
        EventSetDescriptor[] result;
        if (events.size() == 0) {
            result = EMPTY_EVENTSETDESCRIPTORS;
        } else {
            result = new EventSetDescriptor[events.size()];
            result = (EventSetDescriptor[])(EventSetDescriptor[])events.values().toArray(result);
            if (defaultEventName != null) {
                for (int i = 0; i < result.length; i++) {
                    if (defaultEventName.equals(result[i].getName())) {
                        defaultEventIndex = i;
                    }
                }
            }
        }
        return result;
    }
    
    private void addEvent(EventSetDescriptor esd) {
        String key = esd.getName();
        if (esd.getName().equals("propertyChange")) {
            propertyChangeSource = true;
        }
        EventSetDescriptor old = (EventSetDescriptor)(EventSetDescriptor)events.get(key);
        if (old == null) {
            events.put(key, esd);
            return;
        }
        EventSetDescriptor composite = new EventSetDescriptor(old, esd);
        events.put(key, composite);
    }
    
    private MethodDescriptor[] getTargetMethodInfo() {
        if (methods == null) {
            methods = new HashMap(100);
        }
        MethodDescriptor[] explicitMethods = null;
        if (explicitBeanInfo != null) {
            explicitMethods = explicitBeanInfo.getMethodDescriptors();
        }
        if (explicitMethods == null && superBeanInfo != null) {
            MethodDescriptor[] supers = superBeanInfo.getMethodDescriptors();
            for (int i = 0; i < supers.length; i++) {
                addMethod(supers[i]);
            }
        }
        for (int i = 0; i < additionalBeanInfo.length; i++) {
            MethodDescriptor[] additional = additionalBeanInfo[i].getMethodDescriptors();
            if (additional != null) {
                for (int j = 0; j < additional.length; j++) {
                    addMethod(additional[j]);
                }
            }
        }
        if (explicitMethods != null) {
            for (int i = 0; i < explicitMethods.length; i++) {
                addMethod(explicitMethods[i]);
            }
        } else {
            Method[] methodList = getPublicDeclaredMethods(beanClass);
            for (int i = 0; i < methodList.length; i++) {
                Method method = methodList[i];
                if (method == null) {
                    continue;
                }
                MethodDescriptor md = new MethodDescriptor(method);
                addMethod(md);
            }
        }
        MethodDescriptor[] result = new MethodDescriptor[methods.size()];
        result = (MethodDescriptor[])(MethodDescriptor[])methods.values().toArray(result);
        return result;
    }
    
    private void addMethod(MethodDescriptor md) {
        String name = md.getName();
        MethodDescriptor old = (MethodDescriptor)(MethodDescriptor)methods.get(name);
        if (old == null) {
            methods.put(name, md);
            return;
        }
        String[] p1 = md.getParamNames();
        String[] p2 = old.getParamNames();
        boolean match = false;
        if (p1.length == p2.length) {
            match = true;
            for (int i = 0; i < p1.length; i++) {
                if (p1[i] != p2[i]) {
                    match = false;
                    break;
                }
            }
        }
        if (match) {
            MethodDescriptor composite = new MethodDescriptor(old, md);
            methods.put(name, composite);
            return;
        }
        String longKey = makeQualifiedMethodName(name, p1);
        old = (MethodDescriptor)(MethodDescriptor)methods.get(longKey);
        if (old == null) {
            methods.put(longKey, md);
            return;
        }
        MethodDescriptor composite = new MethodDescriptor(old, md);
        methods.put(longKey, composite);
    }
    
    private static String makeQualifiedMethodName(String name, String[] params) {
        StringBuffer sb = new StringBuffer(name);
        sb.append('=');
        for (int i = 0; i < params.length; i++) {
            sb.append(':');
            sb.append(params[i]);
        }
        return sb.toString();
    }
    
    private int getTargetDefaultEventIndex() {
        return defaultEventIndex;
    }
    
    private int getTargetDefaultPropertyIndex() {
        return defaultPropertyIndex;
    }
    
    private BeanDescriptor getTargetBeanDescriptor() {
        if (explicitBeanInfo != null) {
            BeanDescriptor bd = explicitBeanInfo.getBeanDescriptor();
            if (bd != null) {
                return (bd);
            }
        }
        return (new BeanDescriptor(beanClass));
    }
    
    private boolean isEventHandler(Method m) {
        Class[] argTypes = m.getParameterTypes();
        if (argTypes.length != 1) {
            return false;
        }
        if (isSubclass(argTypes[0], .java.util.EventObject.class)) {
            return true;
        }
        return false;
    }
    
    private static synchronized Method[] getPublicDeclaredMethods(Class clz) {
        Method[] result = null;
        if (!ReflectUtil.isPackageAccessible(clz)) {
            return new Method[0];
        }
        final Class fclz = clz;
        Reference ref = (Reference)(Reference)declaredMethodCache.get(fclz);
        if (ref != null) {
            result = (Method[])(Method[])ref.get();
            if (result != null) {
                return result;
            }
        }
        result = (Method[])(Method[])AccessController.doPrivileged(new Introspector$1(fclz));
        for (int i = 0; i < result.length; i++) {
            Method method = result[i];
            int mods = method.getModifiers();
            if (!Modifier.isPublic(mods)) {
                result[i] = null;
            }
        }
        declaredMethodCache.put(fclz, new SoftReference(result));
        return result;
    }
    
    private static Method internalFindMethod(Class start, String methodName, int argCount, Class[] args) {
        Method method = null;
        for (Class cl = start; cl != null; cl = cl.getSuperclass()) {
            Method[] methods = getPublicDeclaredMethods(cl);
            for (int i = 0; i < methods.length; i++) {
                method = methods[i];
                if (method == null) {
                    continue;
                }
                Class[] params = method.getParameterTypes();
                if (method.getName().equals(methodName) && params.length == argCount) {
                    if (args != null) {
                        boolean different = false;
                        if (argCount > 0) {
                            for (int j = 0; j < argCount; j++) {
                                if (params[j] != args[j]) {
                                    different = true;
                                    continue;
                                }
                            }
                            if (different) {
                                continue;
                            }
                        }
                    }
                    return method;
                }
            }
        }
        method = null;
        Class[] ifcs = start.getInterfaces();
        for (int i = 0; i < ifcs.length; i++) {
            method = internalFindMethod(ifcs[i], methodName, argCount, null);
            if (method != null) {
                break;
            }
        }
        return method;
    }
    
    static Method findMethod(Class cls, String methodName, int argCount) {
        return findMethod(cls, methodName, argCount, null);
    }
    
    static Method findMethod(Class cls, String methodName, int argCount, Class[] args) {
        if (methodName == null) {
            return null;
        }
        return internalFindMethod(cls, methodName, argCount, args);
    }
    
    static boolean isSubclass(Class a, Class b) {
        if (a == b) {
            return true;
        }
        if (a == null || b == null) {
            return false;
        }
        for (Class x = a; x != null; x = x.getSuperclass()) {
            if (x == b) {
                return true;
            }
            if (b.isInterface()) {
                Class[] interfaces = x.getInterfaces();
                for (int i = 0; i < interfaces.length; i++) {
                    if (isSubclass(interfaces[i], b)) {
                        return true;
                    }
                }
            }
        }
        return false;
    }
    
    private boolean throwsException(Method method, Class exception) {
        Class[] exs = method.getExceptionTypes();
        for (int i = 0; i < exs.length; i++) {
            if (exs[i] == exception) {
                return true;
            }
        }
        return false;
    }
    
    static Object instantiate(Class sibling, String className) throws InstantiationException, IllegalAccessException, ClassNotFoundException {
        ClassLoader cl = sibling.getClassLoader();
        if (cl != null) {
            try {
                Class cls = cl.loadClass(className);
                return cls.newInstance();
            } catch (Exception ex) {
            }
        }
        try {
            cl = ClassLoader.getSystemClassLoader();
            if (cl != null) {
                Class cls = cl.loadClass(className);
                return cls.newInstance();
            }
        } catch (Exception ex) {
        }
        cl = Thread.currentThread().getContextClassLoader();
        Class cls = cl.loadClass(className);
        return cls.newInstance();
    }
}
