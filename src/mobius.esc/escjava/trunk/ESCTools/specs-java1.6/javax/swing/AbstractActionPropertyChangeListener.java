package javax.swing;

import java.beans.PropertyChangeListener;
import java.lang.ref.WeakReference;
import java.lang.ref.ReferenceQueue;

abstract class AbstractActionPropertyChangeListener implements PropertyChangeListener {
    private static ReferenceQueue queue;
    private WeakReference target;
    private Action action;
    
    AbstractActionPropertyChangeListener(JComponent c, Action a) {
        
        setTarget(c);
        this.action = a;
    }
    
    public void setTarget(JComponent c) {
        if (queue == null) {
            queue = new ReferenceQueue();
        }
        AbstractActionPropertyChangeListener$OwnedWeakReference r;
        while ((r = (AbstractActionPropertyChangeListener$OwnedWeakReference)(AbstractActionPropertyChangeListener$OwnedWeakReference)queue.poll()) != null) {
            AbstractActionPropertyChangeListener oldPCL = (AbstractActionPropertyChangeListener)(AbstractActionPropertyChangeListener)r.getOwner();
            Action oldAction = oldPCL.getAction();
            if (oldAction != null) {
                oldAction.removePropertyChangeListener(oldPCL);
            }
        }
        this.target = new AbstractActionPropertyChangeListener$OwnedWeakReference(c, queue, this);
    }
    
    public JComponent getTarget() {
        return (JComponent)(JComponent)this.target.get();
    }
    
    public Action getAction() {
        return action;
    }
    {
    }
}
