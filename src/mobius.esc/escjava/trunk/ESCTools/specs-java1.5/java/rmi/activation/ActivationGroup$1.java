package java.rmi.activation;

import java.net.MalformedURLException;
import java.rmi.server.RMIClassLoader;
import java.security.PrivilegedExceptionAction;

class ActivationGroup$1 implements PrivilegedExceptionAction {
    /*synthetic*/ final String val$className;
    /*synthetic*/ final ActivationGroupDesc val$desc;
    
    ActivationGroup$1(/*synthetic*/ final ActivationGroupDesc val$desc, /*synthetic*/ final String val$className) throws ClassNotFoundException, MalformedURLException {
        this.val$desc = val$desc;
        this.val$className = val$className;
        
    }
    
    public Object run() throws ClassNotFoundException, MalformedURLException {
        return RMIClassLoader.loadClass(val$desc.getLocation(), val$className);
    }
}
