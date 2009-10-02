package javax.security.auth;

class Policy$3 implements java.security.PrivilegedExceptionAction {
    /*synthetic*/ final String val$finalClass;
    
    Policy$3(/*synthetic*/ final String val$finalClass) throws IllegalAccessException, InstantiationException, ClassNotFoundException {
        this.val$finalClass = val$finalClass;
        
    }
    
    public Object run() throws ClassNotFoundException, InstantiationException, IllegalAccessException {
        return Class.forName(val$finalClass, true, Policy.access$000()).newInstance();
    }
}
