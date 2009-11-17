package javax.print;

import java.util.ArrayList;
import java.util.Iterator;
import sun.misc.Service;

class PrintServiceLookup$1 implements java.security.PrivilegedExceptionAction {
    
    PrintServiceLookup$1() {
        
    }
    
    public Object run() {
        Iterator iterator = Service.providers(PrintServiceLookup.class);
        ArrayList los = PrintServiceLookup.access$200();
        while (iterator.hasNext()) {
            try {
                PrintServiceLookup lus = (PrintServiceLookup)(PrintServiceLookup)iterator.next();
                los.add(lus);
            } catch (Exception e) {
            }
        }
        return null;
    }
}
