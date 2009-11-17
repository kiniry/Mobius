package java.rmi.activation;

import java.rmi.activation.UnknownGroupException;
import java.rmi.activation.UnknownObjectException;
import java.rmi.Remote;
import java.rmi.RemoteException;
import java.rmi.MarshalledObject;
import java.rmi.NoSuchObjectException;
import java.rmi.server.*;
import sun.rmi.server.ActivatableServerRef;

public abstract class Activatable extends RemoteServer {
    private ActivationID id;
    private static final long serialVersionUID = -3120617863591563455L;
    
    protected Activatable(String location, MarshalledObject data, boolean restart, int port) throws ActivationException, RemoteException {
        
        id = exportObject(this, location, data, restart, port);
    }
    
    protected Activatable(String location, MarshalledObject data, boolean restart, int port, RMIClientSocketFactory csf, RMIServerSocketFactory ssf) throws ActivationException, RemoteException {
        
        id = exportObject(this, location, data, restart, port, csf, ssf);
    }
    
    protected Activatable(ActivationID id, int port) throws RemoteException {
        
        this.id = id;
        exportObject(this, id, port);
    }
    
    protected Activatable(ActivationID id, int port, RMIClientSocketFactory csf, RMIServerSocketFactory ssf) throws RemoteException {
        
        this.id = id;
        exportObject(this, id, port, csf, ssf);
    }
    
    protected ActivationID getID() {
        return id;
    }
    
    public static Remote register(ActivationDesc desc) throws UnknownGroupException, ActivationException, RemoteException {
        ActivationID id = ActivationGroup.getSystem().registerObject(desc);
        return sun.rmi.server.ActivatableRef.getStub(desc, id);
    }
    
    public static boolean inactive(ActivationID id) throws UnknownObjectException, ActivationException, RemoteException {
        return ActivationGroup.currentGroup().inactiveObject(id);
    }
    
    public static void unregister(ActivationID id) throws UnknownObjectException, ActivationException, RemoteException {
        ActivationGroup.getSystem().unregisterObject(id);
    }
    
    public static ActivationID exportObject(Remote obj, String location, MarshalledObject data, boolean restart, int port) throws ActivationException, RemoteException {
        ActivationDesc desc = new ActivationDesc(obj.getClass().getName(), location, data, restart);
        ActivationID id = ActivationGroup.getSystem().registerObject(desc);
        Remote stub = exportObject(obj, id, port);
        ActivationGroup.currentGroup().activeObject(id, obj);
        return id;
    }
    
    public static ActivationID exportObject(Remote obj, String location, MarshalledObject data, boolean restart, int port, RMIClientSocketFactory csf, RMIServerSocketFactory ssf) throws ActivationException, RemoteException {
        ActivationDesc desc = new ActivationDesc(obj.getClass().getName(), location, data, restart);
        ActivationID id = ActivationGroup.getSystem().registerObject(desc);
        Remote stub = exportObject(obj, id, port, csf, ssf);
        ActivationGroup.currentGroup().activeObject(id, obj);
        return id;
    }
    
    public static Remote exportObject(Remote obj, ActivationID id, int port) throws RemoteException {
        return exportObject(obj, new ActivatableServerRef(id, port));
    }
    
    public static Remote exportObject(Remote obj, ActivationID id, int port, RMIClientSocketFactory csf, RMIServerSocketFactory ssf) throws RemoteException {
        return exportObject(obj, new ActivatableServerRef(id, port, csf, ssf));
    }
    
    public static boolean unexportObject(Remote obj, boolean force) throws NoSuchObjectException {
        return sun.rmi.transport.ObjectTable.unexportObject(obj, force);
    }
    
    private static Remote exportObject(Remote obj, ActivatableServerRef sref) throws RemoteException {
        if (obj instanceof Activatable) {
            ((Activatable)(Activatable)obj).ref = sref;
        }
        return sref.exportObject(obj, null, false);
    }
}
