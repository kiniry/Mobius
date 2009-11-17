package java.rmi.server;

import java.rmi.RemoteException;


public class SkeletonMismatchException extends RemoteException {
    private static final long serialVersionUID = -7780460454818859281L;
    
    
    public SkeletonMismatchException(String s) {
        super(s);
    }
}
