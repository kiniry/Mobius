package java.awt;

import java.awt.Point;
import java.awt.Toolkit;

class Cursor$1 implements java.security.PrivilegedExceptionAction {
    /*synthetic*/ final String val$flocalized;
    /*synthetic*/ final int val$fy;
    /*synthetic*/ final int val$fx;
    /*synthetic*/ final String val$fileName;
    
    Cursor$1(/*synthetic*/ final String val$fileName, /*synthetic*/ final int val$fx, /*synthetic*/ final int val$fy, /*synthetic*/ final String val$flocalized) {
        this.val$fileName = val$fileName;
        this.val$fx = val$fx;
        this.val$fy = val$fy;
        this.val$flocalized = val$flocalized;
        
    }
    
    public Object run() throws Exception {
        Toolkit toolkit = Toolkit.getDefaultToolkit();
        Image image = toolkit.getImage(Cursor.access$100() + val$fileName);
        return toolkit.createCustomCursor(image, new Point(val$fx, val$fy), val$flocalized);
    }
}
