package coqPlugin.prooftask.button;

import jack.plugin.ToolbarButton;

import org.eclipse.jface.action.IAction;

import coqPlugin.prooftask.EvaluateAllProofTask;

public class EvaluateAllButton extends ToolbarButton {
	/**
	 * @see org.eclipse.ui.IActionDelegate#run(IAction)
	 */
	public void run(IAction action)  {
		runProofTask(action, new EvaluateAllProofTask());
	}
}
