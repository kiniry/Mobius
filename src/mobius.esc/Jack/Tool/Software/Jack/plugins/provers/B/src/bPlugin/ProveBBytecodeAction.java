/*
 * Created on Jun 29, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package bPlugin;

import jack.plugin.JackPlugin;
import jack.plugin.prove.ProofTask;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;


public class ProveBBytecodeAction extends ProveBAction {
	protected ProofTask getProofTask(IFile jpo_file, ICompilationUnit c) {
		return new  AtelierBProofTask(JackPlugin.getBytecodeJpoFile(c),c);		
}

}
