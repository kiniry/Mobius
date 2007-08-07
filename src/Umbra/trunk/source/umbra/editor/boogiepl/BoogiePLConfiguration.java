/*
 * @title       "BoogiePL in Umbra"
 * @description "BoobiePL support for Umbra bytecode editor"
 * @copyright   ""
 * @license     ""
 */
package umbra.editor.boogiepl;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;

import umbra.editor.ColorManager;
import umbra.editor.ColorValues;
import umbra.editor.NonRuleBasedDamagerRepairer;
import umbra.editor.parsing.TokenGetter;


/**
 * This class is used by BoogiePL Editor with the matter of
 * double click strategy and color versions. It has been generated
 * automatically and some changes has been made, for example
 * involving special ways of colouring and possibility of
 * changing the coloring styles ('mod' parameter).
 *
 * @author Samuel Willimann (wsamuel@student.ethz.ch)
 * @version a-01
 */
public class BoogiePLConfiguration extends SourceViewerConfiguration {
  /**
   * TODO.
   */
  private BoogiePLDoubleClickStrategy my_dbl_clickstrategy;
  /**
   * TODO.
   */
  private BoogiePLTagScanner my_tag_scanner;

  /**
   * TODO.
   */
  private BoogiePLScanner my_scanner;

  /**
   * The object which menages the allocation of the colours.
   */
  private ColorManager my_color_mngr;

  /**
   * The current colouring style, see {@link ColorValues}.
   */
  private int my_mode;

  /**
   * TODO.
   *
   * @param the_color_manager TODO
   * @param a_mod TODO
   */
  public BoogiePLConfiguration(final ColorManager the_color_manager,
                               final int a_mod) {
    this.my_color_mngr = the_color_manager;
    this.my_mode = a_mod;
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
      BoogiePLPartitionScanner.HEAD,
      BoogiePLPartitionScanner.TAG };
  }

  /**
   * TODO.
   * @param a_source_viewer TODO
   * @param the_content_type TODO
   * @return TODO
   * @see SourceViewerConfiguration#getDoubleClickStrategy(ISourceViewer,
   *                                                       String)
   */
  public final ITextDoubleClickStrategy getDoubleClickStrategy(
    final ISourceViewer a_source_viewer,
    final String the_content_type) {
    if (my_dbl_clickstrategy == null)
      my_dbl_clickstrategy = new BoogiePLDoubleClickStrategy();
    return my_dbl_clickstrategy;
  }

  /**
   * TODO.
   * @return TODO
   */
  protected final BoogiePLScanner getBoogiePLScanner() {
    if (my_scanner == null) {
      my_scanner = new BoogiePLScanner(my_color_mngr, my_mode);
      my_scanner.setDefaultReturnToken(
        TokenGetter.getToken(my_color_mngr, my_mode, ColorValues.DEFAULT));
    }
    return my_scanner;
  }

  /**
   * TODO.
   * @return TODO
   */
  protected final BoogiePLTagScanner getBoogiePLTagScanner() {
    if (my_tag_scanner == null) {
      my_tag_scanner = new BoogiePLTagScanner(my_color_mngr, my_mode);
      my_tag_scanner.setDefaultReturnToken(
        TokenGetter.getToken(my_color_mngr, my_mode, ColorValues.TAG));
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
   * the current values of the fields {@ref #my_color_mngr} and
   * {@ref #my_mode} combined with an abstrac color indication
   * ({@ref ColorValues#HEADER}, {@ref ColorValues#THROWS}).
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
      new DefaultDamagerRepairer(getBoogiePLTagScanner());
    reconciler.setDamager(dr, BoogiePLPartitionScanner.TAG);
    reconciler.setRepairer(dr, BoogiePLPartitionScanner.TAG);

    dr = new DefaultDamagerRepairer(getBoogiePLScanner());
    reconciler.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
    reconciler.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);

    final NonRuleBasedDamagerRepairer ndr =
      TokenGetter.getRepairer(my_color_mngr, my_mode, ColorValues.HEADER);
    reconciler.setDamager(ndr, BoogiePLPartitionScanner.HEAD);
    reconciler.setRepairer(ndr, BoogiePLPartitionScanner.HEAD);

    final NonRuleBasedDamagerRepairer ndr2 =
      TokenGetter.getRepairer(my_color_mngr, my_mode, ColorValues.THROWS);
    reconciler.setDamager(ndr2, BoogiePLPartitionScanner.THROWS);
    reconciler.setRepairer(ndr2, BoogiePLPartitionScanner.THROWS);

    return reconciler;
  }
}
