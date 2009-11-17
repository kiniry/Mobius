package java.io;

import java.security.*;

public final class SerializablePermission extends BasicPermission {
    private String actions;
    
    public SerializablePermission(String name) {
        super(name);
    }
    
    public SerializablePermission(String name, String actions) {
        super(name, actions);
    }
}
