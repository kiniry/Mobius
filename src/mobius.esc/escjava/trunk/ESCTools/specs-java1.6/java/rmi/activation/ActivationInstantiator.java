package java.rmi.activation;

import java.rmi.MarshalledObject;
import java.rmi.Remote;
import java.rmi.RemoteException;

public interface ActivationInstantiator extends Remote {
    
    public MarshalledObject newInstance(ActivationID id, ActivationDesc desc) throws ActivationException, RemoteException;
}
