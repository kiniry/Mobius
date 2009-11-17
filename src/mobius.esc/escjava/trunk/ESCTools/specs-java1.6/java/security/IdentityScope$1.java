package java.security;

class IdentityScope$1 implements PrivilegedAction {
    
    IdentityScope$1() {
        
    }
    
    public Object run() {
        return Security.getProperty("system.scope");
    }
}
