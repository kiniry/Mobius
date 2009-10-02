package java.beans.beancontext;

import java.beans.PropertyChangeEvent;
import java.beans.VetoableChangeListener;
import java.beans.PropertyVetoException;

class BeanContextSupport$2 implements VetoableChangeListener {
    /*synthetic*/ final BeanContextSupport this$0;
    
    BeanContextSupport$2(/*synthetic*/ final BeanContextSupport this$0) throws PropertyVetoException {
        this.this$0 = this$0;
        
    }
    
    public void vetoableChange(PropertyChangeEvent pce) throws PropertyVetoException {
        this$0.vetoableChange(pce);
    }
}
