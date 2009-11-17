package java.rmi.activation;

import java.rmi.MarshalledObject;
import java.rmi.Remote;
import java.rmi.RemoteException;
import java.rmi.activation.UnknownObjectException;

public interface Activator extends Remote {
    
    public MarshalledObject activate(ActivationID id, boolean force) throws ActivationException, UnknownObjectException, RemoteException;
}
