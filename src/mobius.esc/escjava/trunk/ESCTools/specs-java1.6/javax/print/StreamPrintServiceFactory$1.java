package javax.print;

import java.util.ArrayList;
import java.util.Iterator;
import sun.misc.Service;

class StreamPrintServiceFactory$1 implements java.security.PrivilegedExceptionAction {
    
    StreamPrintServiceFactory$1() {
        
    }
    
    public Object run() {
        Iterator iterator = Service.providers(StreamPrintServiceFactory.class);
        ArrayList lof = StreamPrintServiceFactory.access$100();
        while (iterator.hasNext()) {
            try {
                StreamPrintServiceFactory factory = (StreamPrintServiceFactory)(StreamPrintServiceFactory)iterator.next();
                lof.add(factory);
            } catch (Exception e) {
            }
        }
        return null;
    }
}
