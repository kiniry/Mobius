package java.beans.beancontext;

import java.beans.beancontext.BeanContextServiceAvailableEvent;
import java.beans.beancontext.BeanContextServiceRevokedListener;

public interface BeanContextServicesListener extends BeanContextServiceRevokedListener {
    
    void serviceAvailable(BeanContextServiceAvailableEvent bcsae);
}
