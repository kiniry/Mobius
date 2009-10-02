package javax.print;

import java.io.OutputStream;

public abstract class StreamPrintService implements PrintService {
    private OutputStream outStream;
    private boolean disposed = false;
    
    private StreamPrintService() {
        
    }
    {
    }
    
    protected StreamPrintService(OutputStream out) {
        
        this.outStream = out;
    }
    
    public OutputStream getOutputStream() {
        return outStream;
    }
    
    public abstract String getOutputFormat();
    
    public void dispose() {
        disposed = true;
    }
    
    public boolean isDisposed() {
        return disposed;
    }
}
