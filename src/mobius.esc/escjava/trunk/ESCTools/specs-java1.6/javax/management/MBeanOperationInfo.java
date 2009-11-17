package javax.management;

import java.lang.reflect.Method;
import java.util.Arrays;

public class MBeanOperationInfo extends MBeanFeatureInfo implements java.io.Serializable, Cloneable {
    static final long serialVersionUID = -6178860474881375330L;
    static final MBeanOperationInfo[] NO_OPERATIONS = new MBeanOperationInfo[0];
    public static final int INFO = 0;
    public static final int ACTION = 1;
    public static final int ACTION_INFO = 2;
    public static final int UNKNOWN = 3;
    private final String type;
    private final MBeanParameterInfo[] signature;
    private final int impact;
    private final transient boolean immutable;
    
    public MBeanOperationInfo(String description, Method method) throws IllegalArgumentException {
        this(method.getName(), description, methodSignature(method), method.getReturnType().getName(), UNKNOWN);
    }
    
    public MBeanOperationInfo(String name, String description, MBeanParameterInfo[] signature, String type, int impact) throws IllegalArgumentException {
        super(name, description);
        if (signature == null || signature.length == 0) signature = MBeanParameterInfo.NO_PARAMS; else signature = (MBeanParameterInfo[])(MBeanParameterInfo[])signature.clone();
        this.signature = signature;
        this.type = type;
        this.impact = impact;
        this.immutable = MBeanInfo.isImmutableClass(this.getClass(), MBeanOperationInfo.class);
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            return null;
        }
    }
    
    public String getReturnType() {
        return type;
    }
    
    public MBeanParameterInfo[] getSignature() {
        if (signature.length == 0) return signature; else return (MBeanParameterInfo[])(MBeanParameterInfo[])signature.clone();
    }
    
    private MBeanParameterInfo[] fastGetSignature() {
        if (immutable) return signature; else return getSignature();
    }
    
    public int getImpact() {
        return impact;
    }
    
    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof MBeanOperationInfo)) return false;
        MBeanOperationInfo p = (MBeanOperationInfo)(MBeanOperationInfo)o;
        return (p.getName().equals(getName()) && p.getReturnType().equals(getReturnType()) && p.getDescription().equals(getDescription()) && p.getImpact() == getImpact() && Arrays.equals(p.fastGetSignature(), fastGetSignature()));
    }
    
    public int hashCode() {
        return getName().hashCode() ^ getReturnType().hashCode();
    }
    
    private static MBeanParameterInfo[] methodSignature(Method method) {
        final Class[] classes = method.getParameterTypes();
        final MBeanParameterInfo[] params = new MBeanParameterInfo[classes.length];
        for (int i = 0; i < classes.length; i++) {
            final String pn = "p" + (i + 1);
            params[i] = new MBeanParameterInfo(pn, classes[i].getName(), "");
        }
        return params;
    }
}
