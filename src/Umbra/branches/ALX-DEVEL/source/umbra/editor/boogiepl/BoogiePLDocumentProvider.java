/*
 * @title       "BoogiePL in Umbra"
 * @description "BoobiePL support for Umbra bytecode editor"
 * @copyright   ""
 * @license     ""
 */
package umbra.editor.boogiepl;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ClassGen;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.editors.text.FileDocumentProvider;



/**
 * This class has been modificated with relation to the generated automatically
 * to allow adding listener that is responsible for error checking.
 *
 * @author Samuel Willimann (wsamuel@student.ethz.ch)
 * @version a-01
 */
public class BoogiePLDocumentProvider extends FileDocumentProvider {

  /**
   * TODO.
   * @return TODO
   */
  protected final IDocument createEmptyDocument() {
    return new BoogiePLDocument();
  }

  /**
   * The method used to create Document structure when
   * the editor is initialized. An additional listener is installed.
   * It is related to contribution class that allow displaying control label.
   *
   * @param an_element TODO
   * @return TODO
   * @throws CoreException TODO
   */
  protected final IDocument createDocument(final Object an_element)
    throws CoreException {
    if (an_element instanceof IEditorInput) {
      final IDocument document = createEmptyDocument();
      if (setDocumentContent(document, (IEditorInput) an_element,
                             getEncoding(an_element))) {
        setupDocument(an_element, document);
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
   * come from the main editor class.
   *
   * @param an_editor Related Java code editor
   * @param a_java_class JavaClass structure in BCEL
   * @param a_class_gen class generator in BCEL
   * @param an_input input file
   */
  public final void setRelation(final CompilationUnitEditor an_editor,
                                final JavaClass a_java_class,
                                final ClassGen a_class_gen,
                                final IEditorInput an_input) {
    final BoogiePLDocument document = (BoogiePLDocument)getDocument(an_input);
    document.setJavaClass(a_java_class);
    document.setClassGen(a_class_gen);
    document.setRelatedEditor(an_editor);
  }
}
