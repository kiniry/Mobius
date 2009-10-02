package java.beans;

class SimpleBeanInfo$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final SimpleBeanInfo this$0;
    /*synthetic*/ final String val$resourceName;
    /*synthetic*/ final Class val$c;
    
    SimpleBeanInfo$1(/*synthetic*/ final SimpleBeanInfo this$0, /*synthetic*/ final Class val$c, /*synthetic*/ final String val$resourceName) {
        this.this$0 = this$0;
        this.val$c = val$c;
        this.val$resourceName = val$resourceName;
        
    }
    
    public Object run() {
        java.net.URL url;
        if ((url = val$c.getResource(val$resourceName)) == null) {
            return null;
        } else {
            try {
                return url.getContent();
            } catch (java.io.IOException ioe) {
                return null;
            }
        }
    }
}
