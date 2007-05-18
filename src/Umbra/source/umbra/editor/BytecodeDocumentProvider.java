package umbra.editor;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditor;

import umbra.editor.parsing.BytecodePartitionScanner;


/**
 * This class has been modificated with relation to the generated automatically
 * to allow adding listener that is responsible for error checking
 * 
 * @author Wojciech Wąs
 */
public class BytecodeDocumentProvider extends FileDocumentProvider {

	/**
	 * TODO
	 * 
	 * @return
	 */
	protected IDocument createEmptyDocument() {
		return new BytecodeDocument();
	}
	
	/**
	 * The method used to create Document structure when
	 * the editor is initialized. An additional listener is installed.
	 * It is related to contribution class that allow displaying control label.
	 * 
	 * @param TODO
	 * @throws TODO
	 */
	protected IDocument createDocument(Object element) throws CoreException {
		if (element instanceof IEditorInput) {
			IDocument document= createEmptyDocument();
			if (setDocumentContent(document, (IEditorInput) element, getEncoding(element))) {
				setupDocument(element, document);
			}
			IDocumentPartitioner partitioner =
				new FastPartitioner(
					new BytecodePartitionScanner(),
					new String[] {
						BytecodePartitionScanner.TAG,
						BytecodePartitionScanner.HEAD,
						BytecodePartitionScanner.THROWS});
			partitioner.connect(document);
			document.setDocumentPartitioner(partitioner);
			//contribution = BytecodeContribution.inUse();
			//contribution.addListener(document);
			return document;
		}
		return null;
	}

	/**
	 * This method sets relation to Bytecode structures that
	 * come from the main editor class
	 * 
	 * @param editor	Related Java code editor
	 * @param jc		JavaClass structure in BCEL
	 * @param cg		class generator in BCEL
	 * @param input		input file
	 */
	public void setRelation(AbstractDecoratedTextEditor editor, 
			                BytecodeEditor bEditor, 
			                IEditorInput input) {
		BytecodeDocument document = (BytecodeDocument)getDocument(input);
		document.setEditor(bEditor);
		document.setRelatedEditor(editor);
		BytecodeContribution.inUse().addListener(document);
	}
	
}