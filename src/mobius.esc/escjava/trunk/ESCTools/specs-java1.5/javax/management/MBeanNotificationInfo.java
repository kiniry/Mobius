package javax.management;

import java.util.Arrays;

public class MBeanNotificationInfo extends MBeanFeatureInfo implements Cloneable, java.io.Serializable {
    static final long serialVersionUID = -3888371564530107064L;
    private static final String[] NO_TYPES = new String[0];
    static final MBeanNotificationInfo[] NO_NOTIFICATIONS = new MBeanNotificationInfo[0];
    private final String[] types;
    private final transient boolean immutable;
    
    public MBeanNotificationInfo(String[] notifTypes, String name, String description) throws IllegalArgumentException {
        super(name, description);
        if (notifTypes == null) notifTypes = NO_TYPES;
        this.types = notifTypes;
        this.immutable = MBeanInfo.isImmutableClass(this.getClass(), MBeanNotificationInfo.class);
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            return null;
        }
    }
    
    public String[] getNotifTypes() {
        if (types.length == 0) return NO_TYPES; else return (String[])(String[])types.clone();
    }
    
    private String[] fastGetNotifTypes() {
        if (immutable) return types; else return getNotifTypes();
    }
    
    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof MBeanNotificationInfo)) return false;
        MBeanNotificationInfo p = (MBeanNotificationInfo)(MBeanNotificationInfo)o;
        return (p.getName().equals(getName()) && p.getDescription().equals(getDescription()) && Arrays.equals(p.fastGetNotifTypes(), fastGetNotifTypes()));
    }
    
    public int hashCode() {
        int hash = getName().hashCode();
        for (int i = 0; i < types.length; i++) hash ^= types[i].hashCode();
        return hash;
    }
}
