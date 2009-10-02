package java.beans.beancontext;

import java.io.Serializable;

public class BeanContextServicesSupport$BCSSServiceProvider implements Serializable {
    
    BeanContextServicesSupport$BCSSServiceProvider(Class sc, BeanContextServiceProvider bcsp) {
        
        serviceProvider = bcsp;
    }
    
    protected BeanContextServiceProvider getServiceProvider() {
        return serviceProvider;
    }
    protected BeanContextServiceProvider serviceProvider;
}
