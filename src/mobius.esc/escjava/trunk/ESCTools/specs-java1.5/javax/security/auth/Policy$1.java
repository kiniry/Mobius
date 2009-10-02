package javax.security.auth;

class Policy$1 implements java.security.PrivilegedAction {
    
    Policy$1() {
        
    }
    
    public Object run() {
        return Thread.currentThread().getContextClassLoader();
    }
}
