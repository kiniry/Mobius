package javax.management;

import java.lang.reflect.Constructor;
import java.util.Arrays;

public class MBeanConstructorInfo extends MBeanFeatureInfo implements java.io.Serializable, Cloneable {
    static final long serialVersionUID = 4433990064191844427L;
    static final MBeanConstructorInfo[] NO_CONSTRUCTORS = new MBeanConstructorInfo[0];
    private final transient boolean immutable;
    private final MBeanParameterInfo[] signature;
    
    public MBeanConstructorInfo(String description, Constructor constructor) {
        this(constructor.getName(), description, constructorSignature(constructor));
    }
    
    public MBeanConstructorInfo(String name, String description, MBeanParameterInfo[] signature) throws IllegalArgumentException {
        super(name, description);
        if (signature == null || signature.length == 0) signature = MBeanParameterInfo.NO_PARAMS; else signature = (MBeanParameterInfo[])(MBeanParameterInfo[])signature.clone();
        this.signature = signature;
        this.immutable = MBeanInfo.isImmutableClass(this.getClass(), MBeanConstructorInfo.class);
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            return null;
        }
    }
    
    public MBeanParameterInfo[] getSignature() {
        if (signature.length == 0) return signature; else return (MBeanParameterInfo[])(MBeanParameterInfo[])signature.clone();
    }
    
    private MBeanParameterInfo[] fastGetSignature() {
        if (immutable) return signature; else return getSignature();
    }
    
    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof MBeanConstructorInfo)) return false;
        MBeanConstructorInfo p = (MBeanConstructorInfo)(MBeanConstructorInfo)o;
        return (p.getName().equals(getName()) && p.getDescription().equals(getDescription()) && Arrays.equals(p.fastGetSignature(), fastGetSignature()));
    }
    
    public int hashCode() {
        int hash = getName().hashCode();
        MBeanParameterInfo[] sig = fastGetSignature();
        for (int i = 0; i < sig.length; i++) hash ^= sig[i].hashCode();
        return hash;
    }
    
    private static MBeanParameterInfo[] constructorSignature(Constructor cn) {
        final Class[] classes = cn.getParameterTypes();
        final MBeanParameterInfo[] params = new MBeanParameterInfo[classes.length];
        for (int i = 0; i < classes.length; i++) {
            final String pn = "p" + (i + 1);
            params[i] = new MBeanParameterInfo(pn, classes[i].getName(), "");
        }
        return params;
    }
}
