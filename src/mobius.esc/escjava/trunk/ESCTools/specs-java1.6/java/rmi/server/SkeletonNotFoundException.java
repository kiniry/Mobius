package java.rmi.server;

import java.rmi.RemoteException;


public class SkeletonNotFoundException extends RemoteException {
    private static final long serialVersionUID = -7860299673822761231L;
    
    public SkeletonNotFoundException(String s) {
        super(s);
    }
    
    public SkeletonNotFoundException(String s, Exception ex) {
        super(s, ex);
    }
}
