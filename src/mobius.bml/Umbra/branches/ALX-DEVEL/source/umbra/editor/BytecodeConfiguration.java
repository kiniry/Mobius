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

import umbra.editor.parsing.BytecodePartitionScanner;
import umbra.editor.parsing.BytecodeScanner;
import umbra.editor.parsing.BytecodeTagScanner;
import umbra.editor.parsing.TokenGetter;


/**
 * This class is used by the {@ref BytecodeEditor} with the matter of
 * double click strategy and color versions. It has been generated
 * automatically and some changes has been made, for example
 * involving special ways of colouring and possibility of
 * changing the coloring styles ('my_mode' field).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class BytecodeConfiguration extends SourceViewerConfiguration {

  /**
   * This object handles the operation to synchronise a bytecode editor
   * point with the corresponding statement in the Java source code.
   */
  private BytecodeDoubleClickStrategy my_dblClickStrategy;

  /**
   * The bytecode tag scanner object used, in particular, when the presentation
   * of the bytecode file in an editor is reconciled with a change.
   * TODO is it the only purpose? is it right?
   */
  private BytecodeTagScanner my_tag_scanner;
  //@ invariant my_tag_scanner.colorManager == my_color_manager;

  /**
   * The bytecode scanner object used, in particular, when the presentation
   * of the bytecode file in an editor is generated.
   * TODO is it the only purpose? is it right?
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
   * TODO.
   */
  public BytecodeConfiguration() {
    my_mode = Composition.getMod();
    my_color_manager = ColorManager.getColorManager();
  }

  /**
   * @param a_source_viewer a source viewer for which the content types are
   *                        specified
   * @return a table with content types for the given source viewer, in this
   *         case it contains always:
   * <ul>
   *   <li>{@ref IDocument#DEFAULT_CONTENT_TYPE}</li>
   *   <li>{@ref BytecodePartitionScanner#HEAD}</li>
   *   <li>{@ref BytecodePartitionScanner#TAG}</li>
   * </ul>
   * @see SourceViewerConfiguration#getConfiguredContentTypes(ISourceViewer)
   */
  public final String[] getConfiguredContentTypes(
                                   final ISourceViewer a_source_viewer) {
    return new String[] {
      IDocument.DEFAULT_CONTENT_TYPE,
      BytecodePartitionScanner.HEAD,
      BytecodePartitionScanner.TAG };
  }

  /**
   * This method lazily retruns the value of the double click strategy
   * associated with the current bytecode editor (that means in case
   * it is <code>null</code> it creates a new strategy).
   *
   * @param a_source_viewer a source viewer for which the double click strategy
   *                        is set, currently the parameter is not used
   * @param the_content_type the content type for the double click strategy
   * @return the double click strategy associated with the editor, the
   *         actual type is {@ref BytecodeDoubleClickStrategy}
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
   * {@ref BytecodeScanner} object and registers in it a default return
   * token. This is {@ref ColorValues#DEFAULT}.
   *
   * @return the bytecode scanner object
   */
  protected final BytecodeScanner getBytecodeScanner() {
    if (my_scanner == null) {
      my_scanner = new BytecodeScanner(my_color_manager, my_mode);
      my_scanner.setDefaultReturnToken(
        TokenGetter.getToken(my_color_manager, my_mode, ColorValues.DEFAULT));
    }
    return my_scanner;
  }

  /**
   * This method is a lazy getter for the tag scanner object. It checks if the
   * corresponding field is <code>null</code>. If so it generates a new
   * {@ref BytecodeTagScanner} object and registers in it a default return
   * token. This is {@ref ColorValues#TAG}.
   *
   * @return the bytecode tag scanner object
   */
  protected final BytecodeTagScanner getBytecodeTagScanner() {
    if (my_tag_scanner == null) {
      my_tag_scanner = new BytecodeTagScanner(my_color_manager, my_mode);
      my_tag_scanner.setDefaultReturnToken(
        TokenGetter.getToken(my_color_manager, my_mode, ColorValues.TAG));
    }
    return my_tag_scanner;
  }

  /**
   * This method creates a new presentation reconciler
   * ({@ref PresentationReconciler}) and registers in it damagers and
   * repairers for types ({@ref DefaultDamagerRepairer}):
   * <ul>
   *   <li>{@ref BytecodePartitionScanner#TAG},</li>
   *   <li>{@ref IDocument#DEFAULT_CONTENT_TYPE},</li>
   * </ul>
   * and for types ({@ref NonRuleBasedDamagerRepairer}):
   * <ul>
   *   <li>{@ref BytecodePartitionScanner#HEAD},</li>
   *   <li>{@ref BytecodePartitionScanner#THROWS}.</li>
   * </ul>
   * The {@link NonRuleBasedDamagerRepairer} is initialised with
   * the current values of the fields {@link #my_color_manager} and
   * {@link #my_mode} combined with an abstrac color indication
   * ({@link ColorValues#HEADER}, {@link ColorValues#THROWS}).
   *
   * @param a_source_viewer the source viewer for which the reconciler is
   *        returned
   * @return the new, configured presentation reconciler
   * @see SourceViewerConfiguration#getPresentationReconciler(ISourceViewer)
   */
  public final IPresentationReconciler getPresentationReconciler(
             final ISourceViewer a_source_viewer) {
    final PresentationReconciler reconciler = new PresentationReconciler();

    DefaultDamagerRepairer dr =
      new DefaultDamagerRepairer(getBytecodeTagScanner());
    reconciler.setDamager(dr, BytecodePartitionScanner.TAG);
    reconciler.setRepairer(dr, BytecodePartitionScanner.TAG);

    dr = new DefaultDamagerRepairer(getBytecodeScanner());
    reconciler.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
    reconciler.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);

    final NonRuleBasedDamagerRepairer ndr =
      TokenGetter.getRepairer(my_color_manager, my_mode, ColorValues.HEADER);
    reconciler.setDamager(ndr, BytecodePartitionScanner.HEAD);
    reconciler.setRepairer(ndr, BytecodePartitionScanner.HEAD);

    final NonRuleBasedDamagerRepairer ndr2 =
      TokenGetter.getRepairer(my_color_manager, my_mode, ColorValues.THROWS);
    reconciler.setDamager(ndr2, BytecodePartitionScanner.THROWS);
    reconciler.setRepairer(ndr2, BytecodePartitionScanner.THROWS);

    return reconciler;
  }

  /**
   * This method disposes of the operating system resources associated with
   * the colors in the bytecode editor.
   */
  public final void disposeColor() {
    my_color_manager.dispose();
  }
}
