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

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;

import umbra.editor.parsing.BytecodePartitionScanner;
import umbra.lib.BMLParsing;
import umbra.lib.FileNames;
import annot.bcclass.BCClass;
import annot.io.ReadAttributeException;


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
   * This method creates a byte code document with the empty content.
   *
   * @return a fresh {@link BytecodeDocument} object with no content
   */
  protected final IDocument createEmptyDocument() {
    return new BytecodeDocument();
  }

  /**
   * The method used to create {@link IDocument} structure when
   * the editor is initialised. This method checks if the parameter
   * <code>an_element</code> has the type {@link IEditorInput}. In case
   * the type is proper it creates an empty document and then fills its contents
   * with the data in the file associated with <code>an_element</code>. In
   * case the file does not exists, an empty file is created first.
   * Subsequently, the colouring of the document structure is set using
   * {@link BytecodePartitionScanner}. At last the document is added to the
   * event listener associated with the byte code editor (i.e. the one in
   * {@link BytecodeContribution}.
   *
   * @param an_element an element for which we create the document, the actual
   *   type of this object should be {@link IEditorInput}
   * @return the document structure or <code>null</code> in case the parameter
   *   <code>an_element</code> is null or is not {@link IEditorInput}
   * @throws CoreException if the input for <code>an_element</code>
   *   cannot be accessed or for the reasons presented in
   *   {@link org.eclipse.core.resources.IFile#create(java.io.InputStream,
   *          boolean, org.eclipse.core.runtime.IProgressMonitor)}
   * @throws org.eclipse.core.runtime.OperationCanceledException in case the
   *   operation to create the new file was canceled, this may also happen in
   *   case no user canceled the operation
   */
  protected final IDocument createDocument(final Object an_element)
    throws CoreException {
    if (an_element != null && an_element instanceof IFileEditorInput) {
      final IFileEditorInput iInput = (IFileEditorInput) an_element;
      final IDocument document = createEmptyDocument();
      if (!iInput.getFile().isAccessible()) {
        iInput.getFile().create(
          new ByteArrayInputStream(new byte[0]), true, null);

      }
      IFileEditorInput btcfile = iInput;
      if (isClassFile(iInput)) {
        ColorModeContainer.classKnown();
        btcfile = createBTCFile(iInput);

      }
      if (setDocumentContent(document, btcfile,
                   getEncoding(btcfile))) {
        setupDocument(btcfile, document);
      }
      final IDocumentPartitioner partitioner =
        new FastPartitioner(
          new BytecodePartitionScanner(),
          BytecodePartitionScanner.getPreconfiguredContentTypes());
      document.setDocumentPartitioner(partitioner);
      partitioner.connect(document);
      final BytecodeContribution contribution = BytecodeContribution.inUse();
      contribution.addListener(document);
      if (isClassFile(iInput)) {
        ColorModeContainer.classUnknown();
      }
      return document;
    }
    return null;
  }

  /**
   * @param a_input
   * @return
   */
  private IFileEditorInput createBTCFile(final IFileEditorInput a_input) {
    final IPath apath = a_input.getFile().getFullPath();
    try {
      final String pathName = FileNames.getPath(apath).removeLastSegments(1).
        addTrailingSeparator().
        toPortableString();
      final ClassPath cp = new ClassPath(pathName);
      final SyntheticRepository a_repo = SyntheticRepository.getInstance(cp);
      final JavaClass jc = a_repo.findClass(a_input.getFile().getFullPath().
                                            toOSString());
      final BCClass bcc = new BCClass(jc);
      final BMLParsing bmlp = new BMLParsing(bcc);
      final BytecodeDocument a_doc = new BytecodeDocument();
      a_doc.setEditor(null, bmlp); //refresh BCEL structures
      a_doc.setTextWithDeadUpdate(a_doc.printCode()); //this is where the
                                    //textual representation is generated
      final IFile btcFile = FileNames.getBTCFileName(a_input.getFile());
      final FileEditorInput btcInput = new FileEditorInput(btcFile);
      saveDocument(null, btcInput, a_doc, true);
      return btcInput;
    } catch (JavaModelException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (ReadAttributeException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (CoreException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    return null;
  }

  /**
   * Checks if the given {@link FileEditorInput} can be a class file. The check
   * is based only on the extension of the file name.
   *
   * @param a_input the input to check
   * @return <code>true</code> in case the file is a class file,
   *   <code>false</code> otherwise
   */
  private boolean isClassFile(final IFileEditorInput a_input) {
    return a_input.getFile().getFileExtension().equals("class");
  }

  /**
   * This method creates connection between the document specified by
   * <code>an_input</code> object and given editors.
   *
   * This method sets <code>a_bcode_editor</code> as the editor and
   * <code>an_editor</code> as the related editor for a byte code
   * document that works on <code>an_input</code>. Additionally, it adds
   * the document to the event listener for the byte code editor actions.
   *
   * @param an_editor the editor of the Java source code
   * @param a_bcode_editor the byte code editor in which the textual
   *   representation is to be edited
   * @param an_input input file with the textual representation of the byte code
   * @param a_bmlp a BMLLib representation of the class in the document
   */
  public final void setRelation(final CompilationUnitEditor an_editor,
              final BytecodeEditor a_bcode_editor,
              final IEditorInput an_input,
              final BMLParsing a_bmlp) {
    final BytecodeDocument document = (BytecodeDocument)getDocument(an_input);
    document.setEditor(a_bcode_editor, a_bmlp);
    BytecodeContribution.inUse().addListener(document);
  }

}
