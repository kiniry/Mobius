package java.rmi.server;

import java.lang.reflect.Method;
import java.util.WeakHashMap;
import sun.rmi.server.Util;

class RemoteObjectInvocationHandler$MethodToHash_Maps$1 extends WeakHashMap {
    /*synthetic*/ final RemoteObjectInvocationHandler$MethodToHash_Maps this$0;
    
    RemoteObjectInvocationHandler$MethodToHash_Maps$1(/*synthetic*/ final RemoteObjectInvocationHandler$MethodToHash_Maps this$0) {
        this.this$0 = this$0;
        
    }
    
    public synchronized Object get(Object key) {
        Object hash = super.get(key);
        if (hash == null) {
            Method method = (Method)(Method)key;
            hash = new Long(Util.computeMethodHash(method));
            put(method, hash);
        }
        return (Long)(Long)hash;
    }
}
