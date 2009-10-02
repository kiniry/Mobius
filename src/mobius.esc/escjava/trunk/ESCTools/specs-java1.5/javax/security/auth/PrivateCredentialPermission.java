package javax.security.auth;

import java.util.*;
import java.text.MessageFormat;
import java.security.Permission;
import java.security.PermissionCollection;
import java.security.Principal;
import sun.security.util.ResourcesMgr;

public final class PrivateCredentialPermission extends Permission {
    private static final long serialVersionUID = 5284372143517237068L;
    private static final PrivateCredentialPermission$CredOwner[] EMPTY_PRINCIPALS = new PrivateCredentialPermission$CredOwner[0];
    private String credentialClass;
    private Set principals;
    private transient PrivateCredentialPermission$CredOwner[] credOwners;
    private boolean testing = false;
    
    PrivateCredentialPermission(String credentialClass, Set principals) {
        super(credentialClass);
        this.credentialClass = credentialClass;
        synchronized (principals) {
            if (principals.size() == 0) {
                this.credOwners = EMPTY_PRINCIPALS;
            } else {
                this.credOwners = new PrivateCredentialPermission$CredOwner[principals.size()];
                int index = 0;
                Iterator i = principals.iterator();
                while (i.hasNext()) {
                    Principal p = (Principal)(Principal)i.next();
                    this.credOwners[index++] = new PrivateCredentialPermission$CredOwner(p.getClass().getName(), p.getName());
                }
            }
        }
    }
    
    public PrivateCredentialPermission(String name, String actions) {
        super(name);
        if (!"read".equalsIgnoreCase(actions)) throw new IllegalArgumentException(ResourcesMgr.getString("actions can only be \'read\'"));
        init(name);
    }
    
    public String getCredentialClass() {
        return credentialClass;
    }
    
    public String[][] getPrincipals() {
        if (credOwners == null || credOwners.length == 0) {
            return new String[0][0];
        }
        String[][] pArray = new String[credOwners.length][2];
        for (int i = 0; i < credOwners.length; i++) {
            pArray[i][0] = credOwners[i].principalClass;
            pArray[i][1] = credOwners[i].principalName;
        }
        return pArray;
    }
    
    public boolean implies(Permission p) {
        if (p == null || !(p instanceof PrivateCredentialPermission)) return false;
        PrivateCredentialPermission that = (PrivateCredentialPermission)(PrivateCredentialPermission)p;
        if (!impliesCredentialClass(credentialClass, that.credentialClass)) return false;
        return impliesPrincipalSet(credOwners, that.credOwners);
    }
    
    public boolean equals(Object obj) {
        if (obj == this) return true;
        if (!(obj instanceof PrivateCredentialPermission)) return false;
        PrivateCredentialPermission that = (PrivateCredentialPermission)(PrivateCredentialPermission)obj;
        return (this.implies(that) && that.implies(this));
    }
    
    public int hashCode() {
        return this.credentialClass.hashCode();
    }
    
    public String getActions() {
        return "read";
    }
    
    public PermissionCollection newPermissionCollection() {
        return null;
    }
    
    private void init(String name) {
        if (name == null || name.trim().length() == 0) {
            throw new IllegalArgumentException("invalid empty name");
        }
        ArrayList pList = new ArrayList();
        StringTokenizer tokenizer = new StringTokenizer(name, " ", true);
        String principalClass = null;
        String principalName = null;
        if (testing) System.out.println("whole name = " + name);
        credentialClass = tokenizer.nextToken();
        if (testing) System.out.println("Credential Class = " + credentialClass);
        if (tokenizer.hasMoreTokens() == false) {
            MessageFormat form = new MessageFormat(ResourcesMgr.getString("permission name [name] syntax invalid: "));
            Object[] source = {name};
            throw new IllegalArgumentException(form.format(source) + ResourcesMgr.getString("Credential Class not followed by a Principal Class and Name"));
        }
        while (tokenizer.hasMoreTokens()) {
            tokenizer.nextToken();
            principalClass = tokenizer.nextToken();
            if (testing) System.out.println("    Principal Class = " + principalClass);
            if (tokenizer.hasMoreTokens() == false) {
                MessageFormat form = new MessageFormat(ResourcesMgr.getString("permission name [name] syntax invalid: "));
                Object[] source = {name};
                throw new IllegalArgumentException(form.format(source) + ResourcesMgr.getString("Principal Class not followed by a Principal Name"));
            }
            tokenizer.nextToken();
            principalName = tokenizer.nextToken();
            if (!principalName.startsWith("\"")) {
                MessageFormat form = new MessageFormat(ResourcesMgr.getString("permission name [name] syntax invalid: "));
                Object[] source = {name};
                throw new IllegalArgumentException(form.format(source) + ResourcesMgr.getString("Principal Name must be surrounded by quotes"));
            }
            if (!principalName.endsWith("\"")) {
                while (tokenizer.hasMoreTokens()) {
                    principalName = principalName + tokenizer.nextToken();
                    if (principalName.endsWith("\"")) break;
                }
                if (!principalName.endsWith("\"")) {
                    MessageFormat form = new MessageFormat(ResourcesMgr.getString("permission name [name] syntax invalid: "));
                    Object[] source = {name};
                    throw new IllegalArgumentException(form.format(source) + ResourcesMgr.getString("Principal Name missing end quote"));
                }
            }
            if (testing) System.out.println("\tprincipalName = \'" + principalName + "\'");
            principalName = principalName.substring(1, principalName.length() - 1);
            if (principalClass.equals("*") && !principalName.equals("*")) {
                throw new IllegalArgumentException(ResourcesMgr.getString("PrivateCredentialPermission Principal Class can not be a wildcard (*) value if Principal Name is not a wildcard (*) value"));
            }
            if (testing) System.out.println("\tprincipalName = \'" + principalName + "\'");
            pList.add(new PrivateCredentialPermission$CredOwner(principalClass, principalName));
        }
        this.credOwners = new PrivateCredentialPermission$CredOwner[pList.size()];
        pList.toArray((PrivateCredentialPermission$CredOwner[])this.credOwners);
    }
    
    private boolean impliesCredentialClass(String thisC, String thatC) {
        if (thisC == null || thatC == null) return false;
        if (testing) System.out.println("credential class comparison: " + thisC + "/" + thatC);
        if (thisC.equals("*")) return true;
        return thisC.equals(thatC);
    }
    
    private boolean impliesPrincipalSet(PrivateCredentialPermission$CredOwner[] thisP, PrivateCredentialPermission$CredOwner[] thatP) {
        if (thisP == null || thatP == null) return false;
        if (thatP.length == 0) return true;
        if (thisP.length == 0) return false;
        for (int i = 0; i < thisP.length; i++) {
            boolean foundMatch = false;
            for (int j = 0; j < thatP.length; j++) {
                if (thisP[i].implies(thatP[j])) {
                    foundMatch = true;
                    break;
                }
            }
            if (!foundMatch) {
                return false;
            }
        }
        return true;
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        if (getName().indexOf(" ") == -1 && getName().indexOf("\"") == -1) {
            credentialClass = getName();
            credOwners = EMPTY_PRINCIPALS;
        } else {
            init(getName());
        }
    }
    {
    }
}
