package java.awt.print;

import java.awt.AWTError;

class PrinterJob$1 implements java.security.PrivilegedAction {
    
    PrinterJob$1() {
        
    }
    
    public Object run() {
        String nm = System.getProperty("java.awt.printerjob", null);
        try {
            return (PrinterJob)(PrinterJob)Class.forName(nm).newInstance();
        } catch (ClassNotFoundException e) {
            throw new AWTError("PrinterJob not found: " + nm);
        } catch (InstantiationException e) {
            throw new AWTError("Could not instantiate PrinterJob: " + nm);
        } catch (IllegalAccessException e) {
            throw new AWTError("Could not access PrinterJob: " + nm);
        }
    }
}
