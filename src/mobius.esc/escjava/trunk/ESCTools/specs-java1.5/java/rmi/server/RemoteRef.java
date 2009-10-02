package java.rmi.server;

import java.rmi.*;

public interface RemoteRef extends java.io.Externalizable {
    static final long serialVersionUID = 3632638527362204081L;
    static final String packagePrefix = "sun.rmi.server";
    
    Object invoke(Remote obj, java.lang.reflect.Method method, Object[] params, long opnum) throws Exception;
    
    
    RemoteCall newCall(RemoteObject obj, Operation[] op, int opnum, long hash) throws RemoteException;
    
    
    void invoke(RemoteCall call) throws Exception;
    
    
    void done(RemoteCall call) throws RemoteException;
    
    String getRefClass(java.io.ObjectOutput out);
    
    int remoteHashCode();
    
    boolean remoteEquals(RemoteRef obj);
    
    String remoteToString();
}
