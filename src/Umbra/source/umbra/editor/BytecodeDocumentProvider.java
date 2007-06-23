package umbra.editor;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditor;


/**
 * This class has been modificated with relation to the generated automatically
 * to allow adding listener that is responsible for error checking.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeDocumentProvider extends FileDocumentProvider {

  /**
   * TODO
   *
   *
   * @return a fresh {@ref BytecodeDocument} object with no content
   */
  protected final IDocument createEmptyDocument() {
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
  protected final IDocument createDocument(final Object element) throws CoreException {
    if (element instanceof IEditorInput) {
      final IDocument document = createEmptyDocument();
      if (setDocumentContent(document,
                   (IEditorInput) element,
                   getEncoding(element))) {
        setupDocument(element, document);
      } /*
      IDocumentPartitioner partitioner =
        new FastPartitioner(
          new BytecodePartitionScanner(),
          new String[] {
            BytecodePartitionScanner.TAG,
            BytecodePartitionScanner.HEAD,
            BytecodePartitionScanner.THROWS});
      partitioner.connect(document);
      document.setDocumentPartitioner(partitioner);*/
      final BytecodeContribution contribution = BytecodeContribution.inUse();
      contribution.addListener(document);
      return document;
    }
    return null;
  }



  /**
   * This method sets relation to Bytecode structures that
   * come from the main editor class
   *
   * @param editor  Related Java code editor
   * @param jc    JavaClass structure in BCEL
   * @param cg    class generator in BCEL
   * @param input    input file
   */
  public final void setRelation(final AbstractDecoratedTextEditor editor,
              final BytecodeEditor bEditor,
              final IEditorInput input) {
    final BytecodeDocument document = (BytecodeDocument)getDocument(input);
    document.setEditor(bEditor);
    document.setRelatedEditor(editor);
    BytecodeContribution.inUse().addListener(document);
  }
}
