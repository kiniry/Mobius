package java.rmi.activation;

import java.io.IOException;
import java.io.InvalidObjectException;
import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Proxy;
import java.rmi.MarshalledObject;
import java.rmi.Remote;
import java.rmi.RemoteException;
import java.rmi.UnmarshalException;
import java.rmi.server.RemoteObject;
import java.rmi.server.RemoteObjectInvocationHandler;
import java.rmi.server.RemoteRef;
import java.rmi.server.UID;

public class ActivationID implements java.io.Serializable {
    private transient Activator activator;
    private transient UID uid = new UID();
    private static final long serialVersionUID = -4608673054848209235L;
    
    public ActivationID(Activator activator) {
        
        this.activator = activator;
    }
    
    public Remote activate(boolean force) throws ActivationException, UnknownObjectException, RemoteException {
        try {
            MarshalledObject mobj = (MarshalledObject)activator.activate(this, force);
            return (Remote)(Remote)mobj.get();
        } catch (RemoteException e) {
            throw e;
        } catch (IOException e) {
            throw new UnmarshalException("activation failed", e);
        } catch (ClassNotFoundException e) {
            throw new UnmarshalException("activation failed", e);
        }
    }
    
    public int hashCode() {
        return uid.hashCode();
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof ActivationID) {
            ActivationID id = (ActivationID)(ActivationID)obj;
            return (uid.equals(id.uid) && activator.equals(id.activator));
        } else {
            return false;
        }
    }
    
    private void writeObject(java.io.ObjectOutputStream out) throws IOException, ClassNotFoundException {
        out.writeObject(uid);
        RemoteRef ref;
        if (activator instanceof RemoteObject) {
            ref = ((RemoteObject)(RemoteObject)activator).getRef();
        } else if (Proxy.isProxyClass(activator.getClass())) {
            InvocationHandler handler = Proxy.getInvocationHandler(activator);
            if (!(handler instanceof RemoteObjectInvocationHandler)) {
                throw new InvalidObjectException("unexpected invocation handler");
            }
            ref = ((RemoteObjectInvocationHandler)(RemoteObjectInvocationHandler)handler).getRef();
        } else {
            throw new InvalidObjectException("unexpected activator type");
        }
        out.writeUTF(ref.getRefClass(out));
        ref.writeExternal(out);
    }
    
    private void readObject(java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
        uid = (UID)(UID)in.readObject();
        try {
            Class refClass = Class.forName(RemoteRef.packagePrefix + "." + in.readUTF());
            RemoteRef ref = (RemoteRef)(RemoteRef)refClass.newInstance();
            ref.readExternal(in);
            activator = (Activator)(Activator)Proxy.newProxyInstance(null, new Class[]{Activator.class}, new RemoteObjectInvocationHandler(ref));
        } catch (InstantiationException e) {
            throw (IOException)(IOException)new InvalidObjectException("Unable to create remote reference").initCause(e);
        } catch (IllegalAccessException e) {
            throw (IOException)(IOException)new InvalidObjectException("Unable to create remote reference").initCause(e);
        }
    }
}
