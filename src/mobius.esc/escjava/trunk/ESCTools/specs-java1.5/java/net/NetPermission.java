package java.net;

import java.security.*;

public final class NetPermission extends BasicPermission {
    private static final long serialVersionUID = -8343910153355041693L;
    
    public NetPermission(String name) {
        super(name);
    }
    
    public NetPermission(String name, String actions) {
        super(name, actions);
    }
}
