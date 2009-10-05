package java.rmi.activation;

import java.lang.reflect.Constructor;
import java.rmi.MarshalledObject;
import java.rmi.Naming;
import java.rmi.activation.UnknownGroupException;
import java.rmi.activation.UnknownObjectException;
import java.rmi.Remote;
import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;
import java.security.PrivilegedActionException;
import sun.security.action.GetIntegerAction;

public abstract class ActivationGroup extends UnicastRemoteObject implements ActivationInstantiator {
    private ActivationGroupID groupID;
    private ActivationMonitor monitor;
    private long incarnation;
    private static ActivationGroup currGroup;
    private static ActivationGroupID currGroupID;
    private static ActivationSystem currSystem;
    private static boolean canCreate = true;
    private static Class[] groupConstrParams = {ActivationGroupID.class, MarshalledObject.class};
    private static final long serialVersionUID = -7696947875314805420L;
    
    protected ActivationGroup(ActivationGroupID groupID) throws RemoteException {
        
        this.groupID = groupID;
    }
    
    public boolean inactiveObject(ActivationID id) throws ActivationException, UnknownObjectException, RemoteException {
        getMonitor().inactiveObject(id);
        return true;
    }
    
    public abstract void activeObject(ActivationID id, Remote obj) throws ActivationException, UnknownObjectException, RemoteException;
    
    public static synchronized ActivationGroup createGroup(ActivationGroupID id, final ActivationGroupDesc desc, long incarnation) throws ActivationException {
        SecurityManager security = System.getSecurityManager();
        if (security != null) security.checkSetFactory();
        if (currGroup != null) throw new ActivationException("group already exists");
        if (canCreate == false) throw new ActivationException("group deactivated and cannot be recreated");
        try {
            String groupClassName = desc.getClassName();
            if (groupClassName == null) {
                groupClassName = sun.rmi.server.ActivationGroupImpl.class.getName();
            }
            final String className = groupClassName;
            Class cl;
            try {
                cl = (Class)(Class)java.security.AccessController.doPrivileged(new ActivationGroup$1(desc, className));
            } catch (PrivilegedActionException pae) {
                throw new ActivationException("Could not load default group implementation class", pae.getException());
            }
            Constructor constructor = cl.getConstructor(groupConstrParams);
            Object[] params = new Object[]{id, desc.getData()};
            Object obj = constructor.newInstance(params);
            if (obj instanceof ActivationGroup) {
                ActivationGroup newGroup = (ActivationGroup)(ActivationGroup)obj;
                currSystem = id.getSystem();
                newGroup.incarnation = incarnation;
                newGroup.monitor = currSystem.activeGroup(id, newGroup, incarnation);
                currGroup = newGroup;
                currGroupID = id;
                canCreate = false;
            } else {
                throw new ActivationException("group not correct class: " + obj.getClass().getName());
            }
        } catch (java.lang.reflect.InvocationTargetException e) {
            e.getTargetException().printStackTrace();
            throw new ActivationException("exception in group constructor", e.getTargetException());
        } catch (ActivationException e) {
            throw e;
        } catch (Exception e) {
            throw new ActivationException("exception creating group", e);
        }
        return currGroup;
    }
    
    public static synchronized ActivationGroupID currentGroupID() {
        return currGroupID;
    }
    
    static synchronized ActivationGroupID internalCurrentGroupID() throws ActivationException {
        if (currGroupID == null) throw new ActivationException("nonexistent group");
        return currGroupID;
    }
    
    public static synchronized void setSystem(ActivationSystem system) throws ActivationException {
        SecurityManager security = System.getSecurityManager();
        if (security != null) security.checkSetFactory();
        if (currSystem != null) throw new ActivationException("activation system already set");
        currSystem = system;
    }
    
    public static synchronized ActivationSystem getSystem() throws ActivationException {
        if (currSystem == null) {
            try {
                int port;
                port = ((Integer)(Integer)java.security.AccessController.doPrivileged(new GetIntegerAction("java.rmi.activation.port", ActivationSystem.SYSTEM_PORT))).intValue();
                currSystem = (ActivationSystem)(ActivationSystem)Naming.lookup("//:" + port + "/java.rmi.activation.ActivationSystem");
            } catch (Exception e) {
                throw new ActivationException("unable to obtain ActivationSystem", e);
            }
        }
        return currSystem;
    }
    
    protected void activeObject(ActivationID id, MarshalledObject mobj) throws ActivationException, UnknownObjectException, RemoteException {
        getMonitor().activeObject(id, mobj);
    }
    
    protected void inactiveGroup() throws UnknownGroupException, RemoteException {
        try {
            getMonitor().inactiveGroup(groupID, incarnation);
        } finally {
            destroyGroup();
        }
    }
    
    private ActivationMonitor getMonitor() throws RemoteException {
        synchronized (ActivationGroup.class) {
            if (monitor != null) {
                return monitor;
            }
        }
        throw new RemoteException("monitor not received");
    }
    
    private static synchronized void destroyGroup() {
        currGroup = null;
        currGroupID = null;
    }
    
    static synchronized ActivationGroup currentGroup() throws ActivationException {
        if (currGroup == null) {
            throw new ActivationException("group is not active");
        }
        return currGroup;
    }
}
