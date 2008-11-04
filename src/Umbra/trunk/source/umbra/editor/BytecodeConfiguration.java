/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;

import umbra.editor.actions.BytecodeDoubleClickStrategy;
import umbra.editor.parsing.BytecodeCPSecScanner;
import umbra.editor.parsing.BytecodePartitionScanner;
import umbra.editor.parsing.BytecodeScanner;
import umbra.editor.parsing.BytecodeBMLSecScanner;
import umbra.editor.parsing.ColorManager;
import umbra.editor.parsing.ColorValues;
import umbra.editor.parsing.NonRuleBasedDamagerRepairer;
import umbra.editor.parsing.TokenGetter;


/**
 * This class is used by the {@link BytecodeEditor} with the matter of
 * double click strategy and colour versions. It has been generated
 * automatically and some changes has been made, for example
 * involving special ways of colouring and possibility of
 * changing the colouring styles ('my_mode' field).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeConfiguration extends SourceViewerConfiguration {

  /**
   * This object handles the operation to synchronise a byte code editor
   * point with the corresponding statement in the Java source code.
   */
  private BytecodeDoubleClickStrategy my_dblClickStrategy;

  /**
   * The byte code scanner object used to do the colouring and text
   * styling of the byte code areas inside of the BML areas.
   */
  private BytecodeBMLSecScanner my_bml_secscanner;
  //@ invariant my_bml_secscanner.colorManager == my_color_manager;

  /**
   * The byte code scanner object used to do the colouring and text
   * styling of the byte code areas inside constant pool.
   */
  private BytecodeCPSecScanner my_cp_secscanner;

  /**
   * The byte code scanner object used to do the colouring and text
   * styling of the byte code areas outside of the BML areas.
   */
  private BytecodeScanner my_scanner;
  //@ invariant my_scanner.colorManager == my_color_manager;

  /**
   * The object which manages the allocation of the colours.
   * It is shared by all the objects that handle the colouring.
   */
  private ColorManager my_color_manager;

  /**
   * The current colouring style, see {@link ColorValues}.
   */
  private int my_mode;

  /**
   * The constructor retrieves the current colouring mode from the
   * {@link ColorModeContainer} and the current colour manager
   * from {@link ColorManager}.
   */
  public BytecodeConfiguration() {
    my_mode = ColorModeContainer.getMod();
    my_color_manager = ColorManager.getColorManager();
  }

  /**
   * Returns the configured types of byte code textual document areas.
   *
   * @param a_source_viewer a source viewer for which the content types are
   *   specified
   * @return an array with content types for the given source viewer, in this
   *   case it contains always:
   * <ul>
   *   <li>{@link IDocument#DEFAULT_CONTENT_TYPE}</li>
   *   <li>{@link BytecodePartitionScanner#SECTION_HEAD}</li>
   *   <li>{@link BytecodePartitionScanner#SECTION_CP}</li>
   *   <li>{@link BytecodePartitionScanner#SECTION_BML}</li>
   * </ul>
   * @see SourceViewerConfiguration#getConfiguredContentTypes(ISourceViewer)
   */
  public final String[] getConfiguredContentTypes(
                                   final ISourceViewer a_source_viewer) {
    return BytecodePartitionScanner.getPreconfiguredContentTypes();
  }

  /**
   * This method lazily returns the value of the double click strategy
   * associated with the current byte code editor (that means in case
   * it is <code>null</code> it creates a new strategy).
   *
   * @param a_source_viewer a source viewer for which the double click strategy
   *    is set, currently the parameter is not used
   * @param the_content_type the content type for the double click strategy
   * @return the double click strategy associated with the editor, the
   *    actual type is {@link BytecodeDoubleClickStrategy}
   * @see SourceViewerConfiguration#getDoubleClickStrategy(ISourceViewer,
   *                                                       String)
   */
  public final ITextDoubleClickStrategy getDoubleClickStrategy(
                                  final ISourceViewer a_source_viewer,
                                  final String the_content_type) {
    if (my_dblClickStrategy == null)
      my_dblClickStrategy = new BytecodeDoubleClickStrategy();
    return my_dblClickStrategy;
  }

  /**
   * This method is a lazy getter for the scanner object. It checks if the
   * corresponding field is <code>null</code>. If so it generates a new
   * {@link BytecodeScanner} object and registers in it a default return
   * token. This is {@link ColorValues#SLOT_DEFAULT}.
   *
   * @return the byte code scanner object
   */
  protected final BytecodeScanner getBytecodeScanner() {
    if (my_scanner == null) {
      my_scanner = new BytecodeScanner(my_color_manager, my_mode);
      my_scanner.setDefaultReturnToken(
        TokenGetter.getToken(my_color_manager, my_mode,
                             ColorValues.SLOT_DEFAULT));
    }
    return my_scanner;
  }

  /**
   * This method is a lazy getter for the tag scanner object. It checks if the
   * corresponding field is <code>null</code>. If so it generates a new
   * {@link BytecodeBMLSecScanner} object and registers in it a default return
   * token. This is {@link ColorValues#SLOT_TAG}.
   *
   * @return the byte code tag scanner object
   */
  protected final BytecodeBMLSecScanner getBytecodeBMLSecScanner() {
    if (my_bml_secscanner == null) {
      my_bml_secscanner = new BytecodeBMLSecScanner(my_color_manager, my_mode);
      my_bml_secscanner.setDefaultReturnToken(
        TokenGetter.getToken(my_color_manager, my_mode, ColorValues.SLOT_TAG));
    }
    return my_bml_secscanner;
  }

  /**
   * This method is a lazy getter for the tag scanner object. It checks if the
   * corresponding field is <code>null</code>. If so it generates a new
   * {@link BytecodeCPSecScanner} object and registers in it a default return
   * token. This is {@link ColorValues#SLOT_TAG}.
   *
   * @return the byte code tag scanner object
   */
  protected final BytecodeBMLSecScanner getBytecodeCPSecScanner() {
    if (my_cp_secscanner == null) {
      my_cp_secscanner = new BytecodeCPSecScanner(my_color_manager, my_mode);
      my_cp_secscanner.setDefaultReturnToken(
        TokenGetter.getToken(my_color_manager, my_mode, ColorValues.SLOT_TAG));
    }
    return my_bml_secscanner;
  }

  /**
   * This method creates a new presentation reconciler
   * ({@link PresentationReconciler}) and registers in it damagers and
   * repairers for types ({@link DefaultDamagerRepairer}):
   * <ul>
   *   <li>{@link BytecodePartitionScanner#SECTION_BML},</li>
   *   <li>{@link BytecodePartitionScanner#SECTION_CP},</li>
   *   <li>{@link IDocument#DEFAULT_CONTENT_TYPE},</li>
   * </ul>
   * and for types ({@link NonRuleBasedDamagerRepairer}):
   * <ul>
   *   <li>{@link BytecodePartitionScanner#SECTION_HEAD},</li>
   *   <li>{@link BytecodePartitionScanner#SECTION_THROWS}.</li>
   * </ul>
   * The {@link NonRuleBasedDamagerRepairer} is initialised with
   * the current values of the colour manager and the mode number
   * combined with an abstract colour indication
   * ({@link ColorValues#SLOT_HEADER}, {@link ColorValues#SLOT_THROWS}).
   *
   * This method defines how the colouring works in case an edit operation is
   * performed.
   *
   * @param a_source_viewer the source viewer for which the reconciler is
   *   returned
   * @return the new, configured presentation reconciler
   * @see SourceViewerConfiguration#getPresentationReconciler(ISourceViewer)
   */
  public final IPresentationReconciler getPresentationReconciler(
             final ISourceViewer a_source_viewer) {
    final PresentationReconciler reconciler = new PresentationReconciler();

    DefaultDamagerRepairer dr =
      new DefaultDamagerRepairer(getBytecodeBMLSecScanner());
    reconciler.setDamager(dr, BytecodePartitionScanner.SECTION_BML);
    reconciler.setRepairer(dr, BytecodePartitionScanner.SECTION_BML);

    dr = new DefaultDamagerRepairer(getBytecodeCPSecScanner());
    reconciler.setDamager(dr, BytecodePartitionScanner.SECTION_CP);
    reconciler.setRepairer(dr, BytecodePartitionScanner.SECTION_CP);

    dr = new DefaultDamagerRepairer(getBytecodeScanner());
    reconciler.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
    reconciler.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);

    final NonRuleBasedDamagerRepairer ndr =
      TokenGetter.getRepairer(my_color_manager, my_mode,
                              ColorValues.SLOT_HEADER);
    reconciler.setDamager(ndr, BytecodePartitionScanner.SECTION_HEAD);
    reconciler.setRepairer(ndr, BytecodePartitionScanner.SECTION_HEAD);

    final NonRuleBasedDamagerRepairer ndr2 =
      TokenGetter.getRepairer(my_color_manager, my_mode,
                              ColorValues.SLOT_THROWS);
    reconciler.setDamager(ndr2, BytecodePartitionScanner.SECTION_THROWS);
    reconciler.setRepairer(ndr2, BytecodePartitionScanner.SECTION_THROWS);

    return reconciler;
  }

  /**
   * This method disposes of the operating system resources associated with
   * the colours in the byte code editor.
   */
  public final void disposeColor() {
    my_color_manager.dispose();
  }
}
