package java.rmi.registry;

import java.rmi.AccessException;
import java.rmi.AlreadyBoundException;
import java.rmi.NotBoundException;
import java.rmi.Remote;
import java.rmi.RemoteException;

public interface Registry extends Remote {
    public static final int REGISTRY_PORT = 1099;
    
    public Remote lookup(String name) throws RemoteException, NotBoundException, AccessException;
    
    public void bind(String name, Remote obj) throws RemoteException, AlreadyBoundException, AccessException;
    
    public void unbind(String name) throws RemoteException, NotBoundException, AccessException;
    
    public void rebind(String name, Remote obj) throws RemoteException, AccessException;
    
    public String[] list() throws RemoteException, AccessException;
}
