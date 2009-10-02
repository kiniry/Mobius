package java.awt.print;

import java.awt.HeadlessException;
import javax.print.PrintService;
import javax.print.PrintServiceLookup;
import javax.print.StreamPrintServiceFactory;
import javax.print.attribute.PrintRequestAttributeSet;

public abstract class PrinterJob {
    
    public static PrinterJob getPrinterJob() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkPrintJobAccess();
        }
        return (PrinterJob)(PrinterJob)java.security.AccessController.doPrivileged(new PrinterJob$1());
    }
    
    public static PrintService[] lookupPrintServices() {
        return PrintServiceLookup.lookupPrintServices(DocFlavor$SERVICE_FORMATTED.PAGEABLE, null);
    }
    
    public static StreamPrintServiceFactory[] lookupStreamPrintServices(String mimeType) {
        return StreamPrintServiceFactory.lookupStreamPrintServiceFactories(DocFlavor$SERVICE_FORMATTED.PAGEABLE, mimeType);
    }
    
    public PrinterJob() {
        
    }
    
    public PrintService getPrintService() {
        return null;
    }
    
    public void setPrintService(PrintService service) throws PrinterException {
        throw new PrinterException("Setting a service is not supported on this class");
    }
    
    public abstract void setPrintable(Printable painter);
    
    public abstract void setPrintable(Printable painter, PageFormat format);
    
    public abstract void setPageable(Pageable document) throws NullPointerException;
    
    public abstract boolean printDialog() throws HeadlessException;
    
    public boolean printDialog(PrintRequestAttributeSet attributes) throws HeadlessException {
        if (attributes == null) {
            throw new NullPointerException("attributes");
        }
        return printDialog();
    }
    
    public abstract PageFormat pageDialog(PageFormat page) throws HeadlessException;
    
    public PageFormat pageDialog(PrintRequestAttributeSet attributes) throws HeadlessException {
        if (attributes == null) {
            throw new NullPointerException("attributes");
        }
        return pageDialog(defaultPage());
    }
    
    public abstract PageFormat defaultPage(PageFormat page);
    
    public PageFormat defaultPage() {
        return defaultPage(new PageFormat());
    }
    
    public abstract PageFormat validatePage(PageFormat page);
    
    public abstract void print() throws PrinterException;
    
    public void print(PrintRequestAttributeSet attributes) throws PrinterException {
        print();
    }
    
    public abstract void setCopies(int copies);
    
    public abstract int getCopies();
    
    public abstract String getUserName();
    
    public abstract void setJobName(String jobName);
    
    public abstract String getJobName();
    
    public abstract void cancel();
    
    public abstract boolean isCancelled();
}
