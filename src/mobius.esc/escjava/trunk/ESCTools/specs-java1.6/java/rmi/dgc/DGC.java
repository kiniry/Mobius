package java.rmi.dgc;

import java.rmi.*;
import java.rmi.server.ObjID;

public interface DGC extends Remote {
    
    Lease dirty(ObjID[] ids, long sequenceNum, Lease lease) throws RemoteException;
    
    void clean(ObjID[] ids, long sequenceNum, VMID vmid, boolean strong) throws RemoteException;
}
