package javax.management;

import java.lang.reflect.Method;
import java.security.AccessController;
import java.security.PrivilegedAction;
import com.sun.jmx.mbeanserver.GetPropertyAction;

public class MBeanAttributeInfo extends MBeanFeatureInfo implements java.io.Serializable, Cloneable {
    private static final long serialVersionUID;
    static {
        long uid = 8644704819898565848L;
        try {
            PrivilegedAction act = new GetPropertyAction("jmx.serial.form");
            String form = (String)(String)AccessController.doPrivileged(act);
            if ("1.0".equals(form)) uid = 7043855487133450673L;
        } catch (Exception e) {
        }
        serialVersionUID = uid;
    }
    static final MBeanAttributeInfo[] NO_ATTRIBUTES = new MBeanAttributeInfo[0];
    private final String attributeType;
    private final boolean isWrite;
    private final boolean isRead;
    private final boolean is;
    
    public MBeanAttributeInfo(String name, String type, String description, boolean isReadable, boolean isWritable, boolean isIs) throws IllegalArgumentException {
        super(name, description);
        this.attributeType = type;
        this.isRead = isReadable;
        this.isWrite = isWritable;
        if (isIs && !isReadable) {
            throw new IllegalArgumentException("Cannot have an \"is\" getter for a non-readable attribute.");
        }
        if (isIs && (!type.equals("java.lang.Boolean") && (!type.equals("boolean")))) {
            throw new IllegalArgumentException("Cannot have an \"is\" getter for a non-boolean attribute.");
        }
        this.is = isIs;
    }
    
    public MBeanAttributeInfo(String name, String description, Method getter, Method setter) throws IntrospectionException {
        this(name, attributeType(getter, setter), description, (getter != null), (setter != null), isIs(getter));
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            return null;
        }
    }
    
    public String getType() {
        return attributeType;
    }
    
    public boolean isReadable() {
        return isRead;
    }
    
    public boolean isWritable() {
        return isWrite;
    }
    
    public boolean isIs() {
        return is;
    }
    
    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof MBeanAttributeInfo)) return false;
        MBeanAttributeInfo p = (MBeanAttributeInfo)(MBeanAttributeInfo)o;
        return (p.getName().equals(getName()) && p.getType().equals(getType()) && p.getDescription().equals(getDescription()) && p.isReadable() == isReadable() && p.isWritable() == isWritable() && p.isIs() == isIs());
    }
    
    public int hashCode() {
        return getName().hashCode() ^ getType().hashCode();
    }
    
    private static boolean isIs(Method getter) {
        return (getter != null && getter.getName().startsWith("is") && (getter.getReturnType().equals(Boolean.TYPE) || getter.getReturnType().equals(Boolean.class)));
    }
    
    private static String attributeType(Method getter, Method setter) throws IntrospectionException {
        Class type = null;
        if (getter != null) {
            if (getter.getParameterTypes().length != 0) {
                throw new IntrospectionException("bad getter arg count");
            }
            type = getter.getReturnType();
            if (type == Void.TYPE) {
                throw new IntrospectionException("getter " + getter.getName() + " returns void");
            }
        }
        if (setter != null) {
            Class[] params = setter.getParameterTypes();
            if (params.length != 1) {
                throw new IntrospectionException("bad setter arg count");
            }
            if (type == null) type = params[0]; else if (type != params[0]) {
                throw new IntrospectionException("type mismatch between getter and setter");
            }
        }
        if (type == null) {
            throw new IntrospectionException("getter and setter cannot both be null");
        }
        return type.getName();
    }
}
