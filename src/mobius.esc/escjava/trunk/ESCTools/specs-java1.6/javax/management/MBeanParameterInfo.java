package javax.management;

public class MBeanParameterInfo extends MBeanFeatureInfo implements java.io.Serializable, Cloneable {
    static final long serialVersionUID = 7432616882776782338L;
    static final MBeanParameterInfo[] NO_PARAMS = new MBeanParameterInfo[0];
    private final String type;
    
    public MBeanParameterInfo(String name, String type, String description) throws IllegalArgumentException {
        super(name, description);
        this.type = type;
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            return null;
        }
    }
    
    public String getType() {
        return type;
    }
    
    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof MBeanParameterInfo)) return false;
        MBeanParameterInfo p = (MBeanParameterInfo)(MBeanParameterInfo)o;
        return (p.getName().equals(getName()) && p.getType().equals(getType()) && p.getDescription().equals(getDescription()));
    }
    
    public int hashCode() {
        return getName().hashCode() ^ getType().hashCode();
    }
}
