package java.beans.beancontext;

import java.beans.beancontext.BeanContext;
import java.beans.beancontext.BeanContextEvent;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;

public class BeanContextMembershipEvent extends BeanContextEvent {
    
    public BeanContextMembershipEvent(BeanContext bc, Collection changes) {
        super(bc);
        if (changes == null) throw new NullPointerException("BeanContextMembershipEvent constructor:  changes is null.");
        children = changes;
    }
    
    public BeanContextMembershipEvent(BeanContext bc, Object[] changes) {
        super(bc);
        if (changes == null) throw new NullPointerException("BeanContextMembershipEvent:  changes is null.");
        children = Arrays.asList(changes);
    }
    
    public int size() {
        return children.size();
    }
    
    public boolean contains(Object child) {
        return children.contains(child);
    }
    
    public Object[] toArray() {
        return children.toArray();
    }
    
    public Iterator iterator() {
        return children.iterator();
    }
    protected Collection children;
}
