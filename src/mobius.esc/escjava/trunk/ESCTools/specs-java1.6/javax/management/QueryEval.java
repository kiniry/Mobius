package javax.management;

import java.io.Serializable;
import javax.management.MBeanServer;

public abstract class QueryEval implements Serializable {
    
    public QueryEval() {
        
    }
    private static final long serialVersionUID = 2675899265640874796L;
    private static ThreadLocal server = new InheritableThreadLocal();
    
    public void setMBeanServer(MBeanServer s) {
        server.set(s);
    }
    
    public static MBeanServer getMBeanServer() {
        return (MBeanServer)(MBeanServer)server.get();
    }
}
