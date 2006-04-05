package prover.gui.jobs;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.MultiStatus;
import org.eclipse.core.runtime.Status;

import prover.ProverEditorPlugin;


public class ProverStatus {

	public static IStatus getOkStatus() {
		return new Status(IStatus.OK, ProverEditorPlugin.getPluginId(), IStatus.OK, "", null);
	}
	public static IStatus getErrorStatus(String msg1, String msg2) {
		MultiStatus ms = new MultiStatus(ProverEditorPlugin.getPluginId(), IStatus.ERROR,  msg1, null);
		ms.add(new Status(IStatus.ERROR, ProverEditorPlugin.getPluginId(), IStatus.OK, msg2, null));
		return ms;
	}
	public static IStatus getErrorStatus(String msg1, Exception e) {
		MultiStatus ms = new MultiStatus(ProverEditorPlugin.getPluginId(), IStatus.ERROR,  msg1, null);
		ms.add(new Status(IStatus.ERROR, ProverEditorPlugin.getPluginId(), IStatus.OK, "", e));
		return ms;
	}
}
