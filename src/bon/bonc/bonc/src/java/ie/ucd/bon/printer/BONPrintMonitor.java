package ie.ucd.bon.printer;

public interface BONPrintMonitor {

  boolean isCancelled();
  
  void begin(String info, int totalTasks);
  
  void progress(int completed);
  
  void setInfo(String info);
  
  void complete();
  
  void finishWithErrorMessage(String error);
  
  
  public final BONPrintMonitor JUST_PRINTS_MONITOR = new BONPrintMonitor() {
    public void begin(String info, int totalTasks) {}
    public boolean isCancelled() { return false; }
    public void progress(int completed) {}
    public void setInfo(String info) { System.out.println(info); }
    public void complete() { System.out.println("Done.");}
    public void finishWithErrorMessage(String error) { System.out.println(error);}
  };
  
}
