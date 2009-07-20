/*
 * Created on Jun 29, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package simplifyPlugin;

import jack.plugin.JackPlugin;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.jdt.core.ICompilationUnit;


public class ProveSimplifyBytecodeAction extends ProveSimplifyAction {

/*	protected ProofTask getProofTask(IFile jpo_file, ICompilationUnit c) {
			return new  SimplifyProofTask(JackPlugin.getBytecodeJpoFile(c),c);		
	}*/
	
	protected QualifiedName getPropertyName() {
		return JackPlugin.JML_BYTECODE_COMPILED;
	}
	
	protected IFile getJpoFile(ICompilationUnit compilation_unit) {
		return JackPlugin.getBytecodeJpoFile(compilation_unit);
	}

}
