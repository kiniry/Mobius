package javax.print;

import javax.print.attribute.PrintJobAttributeSet;
import javax.print.attribute.PrintRequestAttributeSet;
import javax.print.event.PrintJobAttributeListener;
import javax.print.event.PrintJobListener;
import javax.print.PrintException;

public interface DocPrintJob {
    
    public PrintService getPrintService();
    
    public PrintJobAttributeSet getAttributes();
    
    public void addPrintJobListener(PrintJobListener listener);
    
    public void removePrintJobListener(PrintJobListener listener);
    
    public void addPrintJobAttributeListener(PrintJobAttributeListener listener, PrintJobAttributeSet attributes);
    
    public void removePrintJobAttributeListener(PrintJobAttributeListener listener);
    
    public void print(Doc doc, PrintRequestAttributeSet attributes) throws PrintException;
}
