package java.rmi.server;

import java.rmi.Remote;


public interface Skeleton {
    
    
    void dispatch(Remote obj, RemoteCall theCall, int opnum, long hash) throws Exception;
    
    
    Operation[] getOperations();
}
