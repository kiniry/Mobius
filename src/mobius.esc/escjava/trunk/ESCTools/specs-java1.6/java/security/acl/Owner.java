package java.security.acl;

import java.security.Principal;

public interface Owner {
    
    public boolean addOwner(Principal caller, Principal owner) throws NotOwnerException;
    
    public boolean deleteOwner(Principal caller, Principal owner) throws NotOwnerException, LastOwnerException;
    
    public boolean isOwner(Principal owner);
}
