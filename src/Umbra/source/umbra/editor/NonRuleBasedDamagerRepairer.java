package umbra.editor;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.presentation.IPresentationDamager;
import org.eclipse.jface.text.presentation.IPresentationRepairer;
import org.eclipse.swt.custom.StyleRange;

import umbra.UmbraPlugin;


/**
 * TODO.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class NonRuleBasedDamagerRepairer
  implements IPresentationDamager, IPresentationRepairer {

  /**
   * The document this object works on TODO???
   */
  protected IDocument fDocument;

  /**
   * The default text attribute
   * if non is returned as data by the current token TODO.
   */
  protected TextAttribute fDefaultTextAttribute;

  /**
   * Constructor for NonRuleBasedDamagerRepairer.
   *
   * @param a_default_text_attribute TODO
   */
  public NonRuleBasedDamagerRepairer(
        /*@ non_null @*/ final TextAttribute a_default_text_attribute) {
    fDefaultTextAttribute = a_default_text_attribute;
  }

  /**
   * TODO.
   * @param a_doc TODO
   * @see IPresentationRepairer#setDocument(IDocument)
   */
  public final void setDocument(final IDocument a_doc) {
    fDocument = a_doc;
  }

  /**
   * Returns the end offset of the line that contains the specified offset or
   * if the offset is inside a line delimiter, the end offset of the next line.
   *
   * @param offset the offset whose line end offset must be computed
   * @return the line end offset for the given offset
   * @exception BadLocationException if offset is invalid in the current
   *            document
   */
  protected final int endOfLineOf(final int offset)
    throws BadLocationException {

    IRegion info = fDocument.getLineInformationOfOffset(offset);
    if (offset <= info.getOffset() + info.getLength())
      return info.getOffset() + info.getLength();

    final int line = fDocument.getLineOfOffset(offset);
    try {
      info = fDocument.getLineInformation(line + 1);
      return info.getOffset() + info.getLength();
    } catch (BadLocationException x) {
      return fDocument.getLength();
    }
  }

  /**
   * TODO.
   * @param a_partition TODO
   * @param an_event TODO
   * @param a_doc_partitioning_chngd TODO
   * @return TODO
   * @see IPresentationDamager#getDamageRegion(ITypedRegion, DocumentEvent,
   *                                           boolean)
   */
  public final IRegion getDamageRegion(final ITypedRegion a_partition,
                                       final DocumentEvent an_event,
                                       final boolean a_doc_partitioning_chngd) {
    if (!a_doc_partitioning_chngd) {
      try {

        final IRegion info =
          fDocument.getLineInformationOfOffset(an_event.getOffset());
        final int start = Math.max(a_partition.getOffset(), info.getOffset());

        int end =
          an_event.getOffset() + (an_event.getText() == null ?
                                         an_event.getLength() :
                                         an_event.getText().length());

        if (info.getOffset() <= end &&
            end <= info.getOffset() + info.getLength()) {
          // optimize the case of the same line
          end = info.getOffset() + info.getLength();
        } else
          end = endOfLineOf(end);

        end =
          Math.min(
            a_partition.getOffset() + a_partition.getLength(),
            end);
        return new Region(start, end - start);

      } catch (BadLocationException x) {
        //TODO what should really be here?
        UmbraPlugin.messagelog("BadLocationException in getDamageRegion");
      }
    }
    return a_partition;
  }

  /**
   * This method adds to <code>a_presentation</code> a presentation style
   * to be used to display <code>a_region</code>. The presentation style
   * is defined with the use of {@ref #fDefaultTextAttribute}.
   *
   * @param a_presentation the text presentation to be filled by this repairer
   * @param a_region the damage to be repaired
   * @see IPresentationRepairer#createPresentation(TextPresentation,
   *                                               ITypedRegion)
   */
  public final void createPresentation(final TextPresentation a_presentation,
                                       final ITypedRegion a_region) {
    addRange(
      a_presentation,
      a_region.getOffset(),
      a_region.getLength(),
      fDefaultTextAttribute);
  }

  /**
   * Adds style information to the given text presentation.
   *
   * @param a_presentation the text presentation to be extended
   * @param the_offset the offset of the range to be styled
   * @param the_length the length of the range to be styled
   * @param an_attr the attribute describing the style of the range to be styled
   */
  protected final void addRange(final TextPresentation a_presentation,
                                final int the_offset,
                                final int the_length,
                                final TextAttribute an_attr) {
    if (an_attr != null)
      a_presentation.addStyleRange(
        new StyleRange(
          the_offset,
          the_length,
          an_attr.getForeground(),
          an_attr.getBackground(),
          an_attr.getStyle()));
  }
}
