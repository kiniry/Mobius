package javax.security.auth;

import java.util.*;
import java.text.MessageFormat;
import sun.security.util.ResourcesMgr;

class PrivateCredentialPermission$CredOwner implements java.io.Serializable {
    private static final long serialVersionUID = -5607449830436408266L;
    String principalClass;
    String principalName;
    
    PrivateCredentialPermission$CredOwner(String principalClass, String principalName) {
        
        this.principalClass = principalClass;
        this.principalName = principalName;
    }
    
    public boolean implies(Object obj) {
        if (obj == null || !(obj instanceof PrivateCredentialPermission$CredOwner)) return false;
        PrivateCredentialPermission$CredOwner that = (PrivateCredentialPermission$CredOwner)(PrivateCredentialPermission$CredOwner)obj;
        if (principalClass.equals("*") || principalClass.equals(that.principalClass)) {
            if (principalName.equals("*") || principalName.equals(that.principalName)) {
                return true;
            }
        }
        return false;
    }
    
    public String toString() {
        MessageFormat form = new MessageFormat(ResourcesMgr.getString("CredOwner:\n\tPrincipal Class = class\n\tPrincipal Name = name"));
        Object[] source = {principalClass, principalName};
        return (form.format(source));
    }
}
