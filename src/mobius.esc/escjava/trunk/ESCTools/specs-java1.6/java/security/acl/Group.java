package java.security.acl;

import java.util.Enumeration;
import java.security.Principal;

public interface Group extends Principal {
    
    public boolean addMember(Principal user);
    
    public boolean removeMember(Principal user);
    
    public boolean isMember(Principal member);
    
    public Enumeration members();
}
