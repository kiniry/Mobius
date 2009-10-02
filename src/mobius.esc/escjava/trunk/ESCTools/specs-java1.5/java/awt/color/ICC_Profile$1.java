package java.awt.color;

import sun.awt.color.ProfileActivator;

class ICC_Profile$1 implements ProfileActivator {
    /*synthetic*/ final ICC_Profile this$0;
    
    ICC_Profile$1(/*synthetic*/ final ICC_Profile this$0) {
        this.this$0 = this$0;
        
    }
    
    public void activate() {
        this$0.activateDeferredProfile();
    }
}
