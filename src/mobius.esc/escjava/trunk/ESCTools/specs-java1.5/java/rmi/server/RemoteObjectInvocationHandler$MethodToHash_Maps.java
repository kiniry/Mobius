package java.rmi.server;

import java.util.Map;
import sun.rmi.server.WeakClassHashMap;

class RemoteObjectInvocationHandler$MethodToHash_Maps extends WeakClassHashMap {
    
    RemoteObjectInvocationHandler$MethodToHash_Maps() {
        
    }
    
    protected Map createMap(Class remoteClass) {
        return new RemoteObjectInvocationHandler$MethodToHash_Maps$1(this);
    }
}
