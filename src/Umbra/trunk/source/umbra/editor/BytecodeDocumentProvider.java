/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor;

import java.io.ByteArrayInputStream;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.editors.text.FileDocumentProvider;

import umbra.editor.parsing.BytecodePartitionScanner;


/**
 * This class has been modified with relation to the generated automatically
 * to allow adding listener that is responsible for error checking.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeDocumentProvider extends FileDocumentProvider {

  /**
   * This method creates a bytecode document with the empty content.
   *
   * @return a fresh {@ref BytecodeDocument} object with no content
   */
  protected final IDocument createEmptyDocument() {
    return new BytecodeDocument();
  }

  /**
   * The method used to create {@link IDocument} structure when
   * the editor is initialized. This method checks if the parameter
   * <code>an_element</code> has the type {@link IEditorInput}. In case
   * the type is proper it creates an empty document and then fills its contents
   * with the data in the file associated with <code>an_element</code>. In
   * case the file does not exists, an empty file is created first.
   * Subsequently, the colouring of the document structure is set using
   * {@link BytecodePartitionScanner}. At last the document is added to the
   * event listener associated with the bytecode editor (i.e. the one in
   * {@link BytecodeContribution}.
   *
   * @param an_element an element for which we create the document, the actual
   *   type of this object should be {@link IEditorInput}
   * @return the document structure or <code>null</code> in case the parameter
   *   <code>an_element</code> is null or is not {@link IEditorInput}
   * @throws CoreException if the input for <code>an_element</code>
   *   cannot be accessed or for the reasons presented in
   *   {@ref IFile.create(InputStream, boolean, IProgressMonitor)}
   * @exception org.eclipse.core.runtime.OperationCanceledException in case the
   *   operation to create the new file was cancelled, this may also happen in
   *   case no user cancelled the operation
   */
  protected final IDocument createDocument(final Object an_element)
    throws CoreException {
    if (an_element != null && an_element instanceof IEditorInput) {
      final IEditorInput iInput = (IEditorInput) an_element;
      final IDocument document = createEmptyDocument();
      if (!((IFileEditorInput) iInput).getFile().isAccessible()) {
        ((IFileEditorInput) iInput).getFile().create(
            new ByteArrayInputStream(new byte[0]), true, null);
      }
      if (setDocumentContent(document,
                   (IEditorInput) an_element,
                   getEncoding(an_element))) {
        setupDocument(an_element, document);
      }
      final IDocumentPartitioner partitioner =
        new FastPartitioner(
          new BytecodePartitionScanner(),
          new String[] {
            BytecodePartitionScanner.TAG,
            BytecodePartitionScanner.HEAD,
            BytecodePartitionScanner.THROWS});
      document.setDocumentPartitioner(partitioner);
      partitioner.connect(document);
      final BytecodeContribution contribution = BytecodeContribution.inUse();
      contribution.addListener(document);
      return document;
    }
    return null;
  }



  /**
   * This method creates connection between the document specified by
   * <code>an_input</code> object and given editors.
   *
   * This method sets <code>a_bcode_editor</code> as the editor amd
   * <code>an_editor</code> as the related editor for a bytecode
   * document designated by <code>an_input</code>. Additionally, it adds
   * the document to the event listener for the bytecode editor actions.
   *
   * @param an_editor the editor of the Java source code
   * @param a_bcode_editor the bytecode editor in which the textual
   *   representation is to be edited
   * @param an_input input file with the textual representation of the bytecode
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
