package java.beans.beancontext;

class BeanContextServicesSupport$BCSSChild$BCSSCServiceRef {
    /*synthetic*/ final BeanContextServicesSupport$BCSSChild this$1;
    
    BeanContextServicesSupport$BCSSChild$BCSSCServiceRef(/*synthetic*/ final BeanContextServicesSupport$BCSSChild this$1, BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef scref, boolean isDelegated) {
        this.this$1 = this$1;
        
        serviceClassRef = scref;
        delegated = isDelegated;
    }
    
    void addRef() {
        refCnt++;
    }
    
    int release() {
        return --refCnt;
    }
    
    BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef getServiceClassRef() {
        return serviceClassRef;
    }
    
    boolean isDelegated() {
        return delegated;
    }
    BeanContextServicesSupport$BCSSChild$BCSSCServiceClassRef serviceClassRef;
    int refCnt = 1;
    boolean delegated = false;
}
