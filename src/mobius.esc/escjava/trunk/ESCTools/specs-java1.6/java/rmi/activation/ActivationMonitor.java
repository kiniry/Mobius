package java.rmi.activation;

import java.rmi.MarshalledObject;
import java.rmi.activation.UnknownObjectException;
import java.rmi.activation.UnknownGroupException;
import java.rmi.Remote;
import java.rmi.RemoteException;

public interface ActivationMonitor extends Remote {
    
    public void inactiveObject(ActivationID id) throws UnknownObjectException, RemoteException;
    
    public void activeObject(ActivationID id, MarshalledObject obj) throws UnknownObjectException, RemoteException;
    
    public void inactiveGroup(ActivationGroupID id, long incarnation) throws UnknownGroupException, RemoteException;
}
