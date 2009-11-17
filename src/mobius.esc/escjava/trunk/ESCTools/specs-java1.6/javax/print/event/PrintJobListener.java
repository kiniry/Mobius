package javax.print.event;

public interface PrintJobListener {
    
    public void printDataTransferCompleted(PrintJobEvent pje);
    
    public void printJobCompleted(PrintJobEvent pje);
    
    public void printJobFailed(PrintJobEvent pje);
    
    public void printJobCanceled(PrintJobEvent pje);
    
    public void printJobNoMoreEvents(PrintJobEvent pje);
    
    public void printJobRequiresAttention(PrintJobEvent pje);
}
