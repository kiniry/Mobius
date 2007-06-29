package umbra.editor;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.editors.text.FileDocumentProvider;


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
   * TODO.
   *
   * @param an_editor  Related Java code editor
   * @param a_bcode_editor TODO
   * @param an_input    input file
   */
  public final void setRelation(final CompilationUnitEditor an_editor,
              final BytecodeEditor a_bcode_editor,
              final IEditorInput an_input) {
    final BytecodeDocument document = (BytecodeDocument)getDocument(an_input);
    document.setEditor(a_bcode_editor);
    document.setRelatedEditor(an_editor);
    BytecodeContribution.inUse().addListener(document);
  }
}
