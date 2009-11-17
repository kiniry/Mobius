package javax.management;

import java.util.Arrays;
import java.util.Map;
import java.util.WeakHashMap;
import java.security.AccessController;
import java.security.PrivilegedAction;

public class MBeanInfo implements Cloneable, java.io.Serializable {
    static final long serialVersionUID = -6451021435135161911L;
    private final String description;
    private final String className;
    private final MBeanAttributeInfo[] attributes;
    private final MBeanOperationInfo[] operations;
    private final MBeanConstructorInfo[] constructors;
    private final MBeanNotificationInfo[] notifications;
    private transient int hashCode;
    private final transient boolean immutable;
    
    public MBeanInfo(String className, String description, MBeanAttributeInfo[] attributes, MBeanConstructorInfo[] constructors, MBeanOperationInfo[] operations, MBeanNotificationInfo[] notifications) throws IllegalArgumentException {
        
        this.className = className;
        this.description = description;
        if (attributes == null) attributes = MBeanAttributeInfo.NO_ATTRIBUTES;
        this.attributes = attributes;
        if (operations == null) operations = MBeanOperationInfo.NO_OPERATIONS;
        this.operations = operations;
        if (constructors == null) constructors = MBeanConstructorInfo.NO_CONSTRUCTORS;
        this.constructors = constructors;
        if (notifications == null) notifications = MBeanNotificationInfo.NO_NOTIFICATIONS;
        this.notifications = notifications;
        this.immutable = isImmutableClass(this.getClass(), MBeanInfo.class);
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            return null;
        }
    }
    
    public String getClassName() {
        return className;
    }
    
    public String getDescription() {
        return description;
    }
    
    public MBeanAttributeInfo[] getAttributes() {
        MBeanAttributeInfo[] as = nonNullAttributes();
        if (as.length == 0) return as; else return (MBeanAttributeInfo[])(MBeanAttributeInfo[])as.clone();
    }
    
    private MBeanAttributeInfo[] fastGetAttributes() {
        if (immutable) return nonNullAttributes(); else return getAttributes();
    }
    
    private MBeanAttributeInfo[] nonNullAttributes() {
        return (attributes == null) ? MBeanAttributeInfo.NO_ATTRIBUTES : attributes;
    }
    
    public MBeanOperationInfo[] getOperations() {
        MBeanOperationInfo[] os = nonNullOperations();
        if (os.length == 0) return os; else return (MBeanOperationInfo[])(MBeanOperationInfo[])os.clone();
    }
    
    private MBeanOperationInfo[] fastGetOperations() {
        if (immutable) return nonNullOperations(); else return getOperations();
    }
    
    private MBeanOperationInfo[] nonNullOperations() {
        return (operations == null) ? MBeanOperationInfo.NO_OPERATIONS : operations;
    }
    
    public MBeanConstructorInfo[] getConstructors() {
        MBeanConstructorInfo[] cs = nonNullConstructors();
        if (cs.length == 0) return cs; else return (MBeanConstructorInfo[])(MBeanConstructorInfo[])cs.clone();
    }
    
    private MBeanConstructorInfo[] fastGetConstructors() {
        if (immutable) return nonNullConstructors(); else return getConstructors();
    }
    
    private MBeanConstructorInfo[] nonNullConstructors() {
        return (constructors == null) ? MBeanConstructorInfo.NO_CONSTRUCTORS : constructors;
    }
    
    public MBeanNotificationInfo[] getNotifications() {
        MBeanNotificationInfo[] ns = nonNullNotifications();
        if (ns.length == 0) return ns; else return (MBeanNotificationInfo[])(MBeanNotificationInfo[])ns.clone();
    }
    
    private MBeanNotificationInfo[] fastGetNotifications() {
        if (immutable) return nonNullNotifications(); else return getNotifications();
    }
    
    private MBeanNotificationInfo[] nonNullNotifications() {
        return (notifications == null) ? MBeanNotificationInfo.NO_NOTIFICATIONS : notifications;
    }
    
    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof MBeanInfo)) return false;
        MBeanInfo p = (MBeanInfo)(MBeanInfo)o;
        if (!p.getClassName().equals(getClassName()) || !p.getDescription().equals(getDescription())) return false;
        return (Arrays.equals(p.fastGetAttributes(), fastGetAttributes()) && Arrays.equals(p.fastGetOperations(), fastGetOperations()) && Arrays.equals(p.fastGetConstructors(), fastGetConstructors()) && Arrays.equals(p.fastGetNotifications(), fastGetNotifications()));
    }
    
    public int hashCode() {
        if (hashCode != 0) return hashCode;
        hashCode = getClassName().hashCode() ^ arrayHashCode(fastGetAttributes()) ^ arrayHashCode(fastGetOperations()) ^ arrayHashCode(fastGetConstructors()) ^ arrayHashCode(fastGetNotifications());
        return hashCode;
    }
    
    private static int arrayHashCode(Object[] array) {
        int hash = 0;
        for (int i = 0; i < array.length; i++) hash ^= array[i].hashCode();
        return hash;
    }
    private static final Map immutability = new WeakHashMap();
    
    static boolean isImmutableClass(Class subclass, Class immutableClass) {
        if (subclass == immutableClass) return true;
        synchronized (immutability) {
            Boolean immutable = (Boolean)(Boolean)immutability.get(subclass);
            if (immutable == null) {
                try {
                    PrivilegedAction immutabilityAction = new MBeanInfo$ImmutabilityAction(subclass, immutableClass);
                    immutable = (Boolean)(Boolean)AccessController.doPrivileged(immutabilityAction);
                } catch (Exception e) {
                    immutable = Boolean.FALSE;
                }
                immutability.put(subclass, immutable);
            }
            return immutable.booleanValue();
        }
    }
    {
    }
}
