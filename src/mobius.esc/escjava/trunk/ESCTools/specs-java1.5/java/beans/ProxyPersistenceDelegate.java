package java.beans;

import java.util.Vector;

class ProxyPersistenceDelegate extends PersistenceDelegate {
    
    ProxyPersistenceDelegate() {
        
    }
    
    protected Expression instantiate(Object oldInstance, Encoder out) {
        Class type = oldInstance.getClass();
        java.lang.reflect.Proxy p = (java.lang.reflect.Proxy)(.java.lang.reflect.Proxy)oldInstance;
        java.lang.reflect.InvocationHandler ih = java.lang.reflect.Proxy.getInvocationHandler(p);
        if (ih instanceof EventHandler) {
            EventHandler eh = (EventHandler)(EventHandler)ih;
            Vector args = new Vector();
            args.add(type.getInterfaces()[0]);
            args.add(eh.getTarget());
            args.add(eh.getAction());
            if (eh.getEventPropertyName() != null) {
                args.add(eh.getEventPropertyName());
            }
            if (eh.getListenerMethodName() != null) {
                args.setSize(4);
                args.add(eh.getListenerMethodName());
            }
            return new Expression(oldInstance, EventHandler.class, "create", args.toArray());
        }
        return new Expression(oldInstance, .java.lang.reflect.Proxy.class, "newProxyInstance", new Object[]{type.getClassLoader(), type.getInterfaces(), ih});
    }
}
