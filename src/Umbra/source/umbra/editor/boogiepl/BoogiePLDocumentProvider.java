package umbra.editor.boogiepl;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditor;



/**
 * This class has been modificated with relation to the generated automatically
 * to allow adding listener that is responsible for error checking
 *
 * @author Samuel Willimann
 */
public class BoogiePLDocumentProvider extends FileDocumentProvider {

  /**
   * TODO
   */
  protected final IDocument createEmptyDocument() {
    return new BoogiePLDocument();
  }

  /**
   * The method used to create Document structure when
   * the editor is initialized. An additional listener is installed.
   * It is related to contribution class that allow displaying control label.
   */
  protected final IDocument createDocument(final Object element) throws CoreException {
    if (element instanceof IEditorInput) {
      final IDocument document= createEmptyDocument();
      if (setDocumentContent(document, (IEditorInput) element, getEncoding(element))) {
        setupDocument(element, document);
      }
      final IDocumentPartitioner partitioner =
        new FastPartitioner(
          new BoogiePLPartitionScanner(),
          new String[] {
            BoogiePLPartitionScanner.TAG,
            BoogiePLPartitionScanner.HEAD,
            BoogiePLPartitionScanner.THROWS});
      partitioner.connect(document);
      document.setDocumentPartitioner(partitioner);
      //contribution = BoogiePLContribution.inUse();
      //contribution.addListener(document);
      return document;
    }
    return null;
  }

  /**
   * This method sets relation to BoogiePL structures that
   * come from the main editor class
   *
   * @param editor  Related Java code editor
   * @param jc    JavaClass structure in BCEL
   * @param cg    class generator in BCEL
   * @param input    input file
   */
  public final void setRelation(final AbstractDecoratedTextEditor editor, final JavaClass jc, final ClassGen cg, final IEditorInput input) {
    final BoogiePLDocument document = (BoogiePLDocument)getDocument(input);
    document.setJavaClass(jc);
    document.setClassGen(cg);
    document.setRelatedEditor(editor);
  }
}
