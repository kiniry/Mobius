package javax.print;

import javax.print.attribute.PrintRequestAttributeSet;

public interface MultiDocPrintJob extends DocPrintJob {
    
    public void print(MultiDoc multiDoc, PrintRequestAttributeSet attributes) throws PrintException;
}
