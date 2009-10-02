package javax.security.auth;

public final class AuthPermission extends java.security.BasicPermission {
    private static final long serialVersionUID = 5806031445061587174L;
    
    public AuthPermission(String name) {
        super("createLoginContext".equals(name) ? "createLoginContext.*" : name);
    }
    
    public AuthPermission(String name, String actions) {
        super("createLoginContext".equals(name) ? "createLoginContext.*" : name, actions);
    }
}
