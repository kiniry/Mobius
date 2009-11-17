package java.beans.beancontext;

import java.beans.beancontext.BeanContextMembershipEvent;
import java.util.EventListener;

public interface BeanContextMembershipListener extends EventListener {
    
    void childrenAdded(BeanContextMembershipEvent bcme);
    
    void childrenRemoved(BeanContextMembershipEvent bcme);
}
