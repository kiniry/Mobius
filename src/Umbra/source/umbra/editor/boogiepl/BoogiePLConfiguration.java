package umbra.editor.boogiepl;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;

import umbra.editor.ColorManager;
import umbra.editor.IColorValues;
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
  private BoogiePLDoubleClickStrategy doubleClickStrategy;
  /**
   * TODO.
   */
  private BoogiePLTagScanner tagScanner;
  /**
   * TODO.
   */
  private BoogiePLScanner scanner;

  /**
   * The object which menages the allocation of the colours.
   */
  private ColorManager colorManager;
  /**
   * The current colouring style, see {@link IColorValues}.
   */
  private int mod;

  /**
   * TODO.
   *
   * @param the_color_manager TODO
   * @param a_mod TODO
   */
  public BoogiePLConfiguration(final ColorManager the_color_manager,
                               final int a_mod) {
    this.colorManager = the_color_manager;
    this.mod = a_mod;
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
    if (doubleClickStrategy == null)
      doubleClickStrategy = new BoogiePLDoubleClickStrategy();
    return doubleClickStrategy;
  }

  /**
   * TODO.
   * @return TODO
   */
  protected final BoogiePLScanner getBoogiePLScanner() {
    if (scanner == null) {
      scanner = new BoogiePLScanner(colorManager, mod);
      scanner.setDefaultReturnToken(
        TokenGetter.getToken(colorManager, mod, IColorValues.DEFAULT));
    }
    return scanner;
  }

  /**
   * TODO.
   * @return TODO
   */
  protected final BoogiePLTagScanner getBoogiePLTagScanner() {
    if (tagScanner == null) {
      tagScanner = new BoogiePLTagScanner(colorManager, mod);
      tagScanner.setDefaultReturnToken(
        TokenGetter.getToken(colorManager, mod, IColorValues.TAG));
    }
    return tagScanner;
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
   * the current values of the fields {@ref #colorManager} and
   * {@ref #mod} combined with an abstrac color indication
   * ({@ref IColorValues#HEADER}, {@ref IColorValues#THROWS}).
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
      TokenGetter.getRepairer(colorManager, mod, IColorValues.HEADER);
    reconciler.setDamager(ndr, BoogiePLPartitionScanner.HEAD);
    reconciler.setRepairer(ndr, BoogiePLPartitionScanner.HEAD);

    final NonRuleBasedDamagerRepairer ndr2 =
      TokenGetter.getRepairer(colorManager, mod, IColorValues.THROWS);
    reconciler.setDamager(ndr2, BoogiePLPartitionScanner.THROWS);
    reconciler.setRepairer(ndr2, BoogiePLPartitionScanner.THROWS);

    return reconciler;
  }
}
