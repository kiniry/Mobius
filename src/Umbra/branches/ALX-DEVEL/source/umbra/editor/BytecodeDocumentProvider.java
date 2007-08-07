/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.editors.text.FileDocumentProvider;

import umbra.editor.parsing.BytecodePartitionScanner;


/**
 * This class has been modified with relation to the generated automatically
 * to allow adding listener that is responsible for error checking.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
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
