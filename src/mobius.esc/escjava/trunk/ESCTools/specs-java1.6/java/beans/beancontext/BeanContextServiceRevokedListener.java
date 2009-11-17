package java.beans.beancontext;

import java.beans.beancontext.BeanContextServiceRevokedEvent;
import java.util.EventListener;

public interface BeanContextServiceRevokedListener extends EventListener {
    
    void serviceRevoked(BeanContextServiceRevokedEvent bcsre);
}
