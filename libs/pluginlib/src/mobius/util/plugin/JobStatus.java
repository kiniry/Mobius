package mobius.util.plugin;


import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.MultiStatus;
import org.eclipse.core.runtime.Status;


/**
 * A class to ease the returning of status for the Jobs.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class JobStatus {
  /** the plugin id, used for the return status of the job. */
  private static final String PLUGIN_ID = Activator.PLUGIN_ID;
  
  
  /** */
  private JobStatus() { }
  
  
  /**
   * Returns a standard ok status.
   * @return A standard ok status.
   */
  public static IStatus getOkStatus() {
    return new Status(IStatus.OK, PLUGIN_ID, IStatus.OK, "", null);
  }
  
  /**
   * Return a status with a simple message (msg1) and a more complete one
   * (msg2). 
   * @param msg1 A summary
   * @param msg2 The complete error message.
   * @return A status containing an message plus its summary as specified.
   */
  public static IStatus getErrorStatus(final String msg1, 
                                       final String msg2) {
    final MultiStatus ms = new MultiStatus(PLUGIN_ID, 
                                           IStatus.ERROR,  msg1, null);
    ms.add(new Status(IStatus.ERROR, PLUGIN_ID, IStatus.OK, msg2, null));
    return ms;
  }
  
  
  /**
   * Return an error status easy to handle.
   * @param msg1 A summary of the error.
   * @param e The exception providing the error
   * @return A status containing an error message plus its exception originating it.
   */
  public static IStatus getErrorStatus(final String msg1, final Exception e) {
    final MultiStatus ms = new MultiStatus(PLUGIN_ID, 
                                           IStatus.ERROR,  msg1, null);
    ms.add(new Status(IStatus.ERROR, PLUGIN_ID, IStatus.OK, "", e));
    return ms;
  }
}
