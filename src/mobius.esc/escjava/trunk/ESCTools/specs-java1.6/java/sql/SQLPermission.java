package java.sql;

import java.security.*;

public final class SQLPermission extends BasicPermission {
    
    public SQLPermission(String name) {
        super(name);
    }
    
    public SQLPermission(String name, String actions) {
        super(name, actions);
    }
    static final long serialVersionUID = -1439323187199563495L;
}
