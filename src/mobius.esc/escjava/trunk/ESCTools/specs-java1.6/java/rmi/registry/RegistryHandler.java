package java.rmi.registry;

import java.rmi.RemoteException;
import java.rmi.UnknownHostException;


public interface RegistryHandler {
    
    
    Registry registryStub(String host, int port) throws RemoteException, UnknownHostException;
    
    
    Registry registryImpl(int port) throws RemoteException;
}
