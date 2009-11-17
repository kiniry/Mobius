package javax.security.auth;

class Policy$2 implements java.security.PrivilegedAction {
    
    Policy$2() {
        
    }
    
    public Object run() {
        return java.security.Security.getProperty("auth.policy.provider");
    }
}
