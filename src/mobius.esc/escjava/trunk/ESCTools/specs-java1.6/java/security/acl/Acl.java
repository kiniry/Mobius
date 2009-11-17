package java.security.acl;

import java.util.Enumeration;
import java.security.Principal;

public interface Acl extends Owner {
    
    public void setName(Principal caller, String name) throws NotOwnerException;
    
    public String getName();
    
    public boolean addEntry(Principal caller, AclEntry entry) throws NotOwnerException;
    
    public boolean removeEntry(Principal caller, AclEntry entry) throws NotOwnerException;
    
    public Enumeration getPermissions(Principal user);
    
    public Enumeration entries();
    
    public boolean checkPermission(Principal principal, Permission permission);
    
    public String toString();
}
