package java.beans.beancontext;

import java.io.Serializable;

public class BeanContextSupport$BCSChild implements Serializable {
    /*synthetic*/ final BeanContextSupport this$0;
    private static final long serialVersionUID = -5815286101609939109L;
    
    BeanContextSupport$BCSChild(/*synthetic*/ final BeanContextSupport this$0, Object bcc, Object pee) {
        this.this$0 = this$0;
        
        child = bcc;
        proxyPeer = pee;
    }
    
    Object getChild() {
        return child;
    }
    
    void setRemovePending(boolean v) {
        removePending = v;
    }
    
    boolean isRemovePending() {
        return removePending;
    }
    
    boolean isProxyPeer() {
        return proxyPeer != null;
    }
    
    Object getProxyPeer() {
        return proxyPeer;
    }
    private Object child;
    private Object proxyPeer;
    private transient boolean removePending;
}
