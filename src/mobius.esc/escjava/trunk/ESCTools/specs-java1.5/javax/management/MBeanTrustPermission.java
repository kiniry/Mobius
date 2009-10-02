package javax.management;

import java.security.BasicPermission;

public class MBeanTrustPermission extends BasicPermission {
    private static final long serialVersionUID = -2952178077029018140L;
    
    public MBeanTrustPermission(String name) {
        this(name, null);
    }
    
    public MBeanTrustPermission(String name, String actions) {
        super(name, actions);
        if (actions != null && actions.length() > 0) throw new IllegalArgumentException("MBeanTrustPermission " + "actions must be null: " + actions);
        if (!name.equals("register") && !name.equals("*")) throw new IllegalArgumentException("MBeanTrustPermission: " + "Unknown target name " + "[" + name + "]");
    }
}
