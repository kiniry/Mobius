package java.rmi.server;

import java.rmi.*;
import sun.rmi.server.UnicastServerRef;
import sun.rmi.server.UnicastServerRef2;

public class UnicastRemoteObject extends RemoteServer {
    private int port = 0;
    private RMIClientSocketFactory csf = null;
    private RMIServerSocketFactory ssf = null;
    private static final long serialVersionUID = 4974527148936298033L;
    
    protected UnicastRemoteObject() throws RemoteException {
        this(0);
    }
    
    protected UnicastRemoteObject(int port) throws RemoteException {
        
        this.port = port;
        exportObject((Remote)this, port);
    }
    
    protected UnicastRemoteObject(int port, RMIClientSocketFactory csf, RMIServerSocketFactory ssf) throws RemoteException {
        
        this.port = port;
        this.csf = csf;
        this.ssf = ssf;
        exportObject((Remote)this, port, csf, ssf);
    }
    
    private void readObject(java.io.ObjectInputStream in) throws java.io.IOException, java.lang.ClassNotFoundException {
        in.defaultReadObject();
        reexport();
    }
    
    public Object clone() throws CloneNotSupportedException {
        try {
            UnicastRemoteObject cloned = (UnicastRemoteObject)(UnicastRemoteObject)super.clone();
            cloned.reexport();
            return cloned;
        } catch (RemoteException e) {
            throw new ServerCloneException("Clone failed", e);
        }
    }
    
    private void reexport() throws RemoteException {
        if (csf == null && ssf == null) {
            exportObject((Remote)this, port);
        } else {
            exportObject((Remote)this, port, csf, ssf);
        }
    }
    
    public static RemoteStub exportObject(Remote obj) throws RemoteException {
        return (RemoteStub)(RemoteStub)exportObject(obj, new UnicastServerRef(true));
    }
    
    public static Remote exportObject(Remote obj, int port) throws RemoteException {
        return exportObject(obj, new UnicastServerRef(port));
    }
    
    public static Remote exportObject(Remote obj, int port, RMIClientSocketFactory csf, RMIServerSocketFactory ssf) throws RemoteException {
        return exportObject(obj, new UnicastServerRef2(port, csf, ssf));
    }
    
    public static boolean unexportObject(Remote obj, boolean force) throws java.rmi.NoSuchObjectException {
        return sun.rmi.transport.ObjectTable.unexportObject(obj, force);
    }
    
    private static Remote exportObject(Remote obj, UnicastServerRef sref) throws RemoteException {
        if (obj instanceof UnicastRemoteObject) {
            ((UnicastRemoteObject)(UnicastRemoteObject)obj).ref = sref;
        }
        return sref.exportObject(obj, null, false);
    }
}
