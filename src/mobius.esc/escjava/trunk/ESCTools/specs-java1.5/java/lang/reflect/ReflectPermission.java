package java.lang.reflect;

public final class ReflectPermission extends java.security.BasicPermission {
    private static final long serialVersionUID = 7412737110241507485L;
    
    public ReflectPermission(String name) {
        super(name);
    }
    
    public ReflectPermission(String name, String actions) {
        super(name, actions);
    }
}
