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
 * This class is used by the Bytecode Editor with the matter of
 * double click strategy and color versions. It has been generated
 * automatically and some changes has been made, for example
 * involving special ways of colouring and possibility of
 * changing the coloring styles ('mod' parameter).
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
   * TODO
   */
  private BytecodeTagScanner tagScanner;
  //@ invariant tagScanner.colorManager == colorManager;

  /**
   * TODO
   */
  private BytecodeScanner scanner;
  //@ invariant scanner.colorManager == colorManager;

  /**
   * The object which manages the allocation of the colours.
   * It is shared by all the objects that handle the colouring.
   */
  private ColorManager colorManager;

  /**
   * The current colouring style, see {@link IColorValues}
   */
  private int mod;

  /**
   * TODO
   */
  public BytecodeConfiguration() {
    mod = Composition.getMod();
    colorManager = ColorManager.getColorManager();
  }

  /**
   * TODO
   */
  public final String[] getConfiguredContentTypes(final ISourceViewer sourceViewer) {
    return new String[] {
      IDocument.DEFAULT_CONTENT_TYPE,
      BytecodePartitionScanner.HEAD,
      BytecodePartitionScanner.TAG };
  }

  /**
   * TODO
   */
  public final ITextDoubleClickStrategy getDoubleClickStrategy(
    final ISourceViewer sourceViewer,
    final String contentType) {
    if (my_dblClickStrategy == null)
      my_dblClickStrategy = new BytecodeDoubleClickStrategy();
    return my_dblClickStrategy;
  }

  /**
   * TODO
   *
   * @return
   */
  protected final BytecodeScanner getBytecodeScanner() {
    if (scanner == null) {
      scanner = new BytecodeScanner(colorManager, mod);
      scanner.setDefaultReturnToken(
        TokenGetter.getToken(colorManager, mod, IColorValues.DEFAULT));
    }
    return scanner;
  }

  /**
   * TODO
   */
  protected final BytecodeTagScanner getBytecodeTagScanner() {
    if (tagScanner == null) {
      tagScanner = new BytecodeTagScanner(colorManager, mod);
      tagScanner.setDefaultReturnToken(
        TokenGetter.getToken(colorManager, mod, IColorValues.TAG));
    }
    return tagScanner;
  }

  /**
   * TODO
   */
  public final IPresentationReconciler getPresentationReconciler(
             final ISourceViewer sourceViewer) {
    final PresentationReconciler reconciler = new PresentationReconciler();

    DefaultDamagerRepairer dr =
      new DefaultDamagerRepairer(getBytecodeTagScanner());
    reconciler.setDamager(dr, BytecodePartitionScanner.TAG);
    reconciler.setRepairer(dr, BytecodePartitionScanner.TAG);

    dr = new DefaultDamagerRepairer(getBytecodeScanner());
    reconciler.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
    reconciler.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);

    final NonRuleBasedDamagerRepairer ndr =
      TokenGetter.getRepairer(colorManager, mod, IColorValues.HEADER);
    reconciler.setDamager(ndr, BytecodePartitionScanner.HEAD);
    reconciler.setRepairer(ndr, BytecodePartitionScanner.HEAD);

    final NonRuleBasedDamagerRepairer ndr2 =
      TokenGetter.getRepairer(colorManager, mod, IColorValues.THROWS);
    reconciler.setDamager(ndr2, BytecodePartitionScanner.THROWS);
    reconciler.setRepairer(ndr2, BytecodePartitionScanner.THROWS);

    return reconciler;
  }

  /**
   * TODO
   *
   */
  public final void disposeColor() {
    colorManager.dispose();
  }
}
