package mobius.prover.gui.jobs;

/**
 * Jobs to append some text to viewers.
 * To schedule this Job the {@link #prepare()} method shall be used
 * instead of the usual {@link org.eclipse.ui.progress.Job#schedule()}.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public interface IAppendJob {

  /**
   * Prepare the string to be append and then schedule
   * the Job. It is to be used instead of 
   * {@link org.eclipse.ui.progress.Job#schedule()}.
   */
  void prepare();
  
  /**
   * Add the specified string to be append to the target document.
   * @param str The string to append
   */
  void add(String str);
  
  /**
   * Add the specified StringBuffer to be append to the target document.
   * @param str The string to append
   */
  void add(StringBuffer str);
  
  /**
   * Returns the length of the String to add to the document.
   * @return the length, superior to 0.
   */
  int getLength();
}
