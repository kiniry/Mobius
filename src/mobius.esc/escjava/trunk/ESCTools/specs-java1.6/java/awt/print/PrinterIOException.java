package java.awt.print;

import java.io.IOException;

public class PrinterIOException extends PrinterException {
    static final long serialVersionUID = 5850870712125932846L;
    private IOException mException;
    
    public PrinterIOException(IOException exception) {
        
        initCause(null);
        mException = exception;
    }
    
    public IOException getIOException() {
        return mException;
    }
    
    public Throwable getCause() {
        return mException;
    }
}
