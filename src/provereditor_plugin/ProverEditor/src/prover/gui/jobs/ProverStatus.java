package prover.gui.jobs;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.MultiStatus;
import org.eclipse.core.runtime.Status;

import prover.ProverEditorPlugin;

/**
 * A class to ease the returning of status for the Jobs.
 * @author J. Charles
 */
public class ProverStatus {
	/**
	 * Returns a standard ok status.
	 * @return A standard ok status.
	 */
	public static IStatus getOkStatus() {
		return new Status(IStatus.OK, ProverEditorPlugin.PLUGIN_ID, IStatus.OK, "", null);
	}
	
	/**
	 * Return a status with a simple message (msg1) and a more complete one
	 * (msg2). 
	 * @param msg1 A summary
	 * @param msg2 The complete error message.
	 * @return A status containing an message plus its summary as specified.
	 */
	public static IStatus getErrorStatus(String msg1, String msg2) {
		MultiStatus ms = new MultiStatus(ProverEditorPlugin.PLUGIN_ID, IStatus.ERROR,  msg1, null);
		ms.add(new Status(IStatus.ERROR, ProverEditorPlugin.PLUGIN_ID, IStatus.OK, msg2, null));
		return ms;
	}
	
	
	/**
	 * Return an error status easy to handle.
	 * @param msg1 A summary of the error.
	 * @param e The exception providing the error
	 * @return A status containing an error message plus its exception originating it.
	 */
	public static IStatus getErrorStatus(String msg1, Exception e) {
		MultiStatus ms = new MultiStatus(ProverEditorPlugin.PLUGIN_ID, IStatus.ERROR,  msg1, null);
		ms.add(new Status(IStatus.ERROR, ProverEditorPlugin.PLUGIN_ID, IStatus.OK, "", e));
		return ms;
	}
}
