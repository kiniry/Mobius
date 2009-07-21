/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;

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

import umbra.editor.BytecodeDocument;
import umbra.lib.GUIMessages;
import umbra.lib.UmbraLocationException;


/**
 * This class is responsible for colouring these areas in a byte code
 * editor window which are inside one-line areas.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Wojciech Was (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class NonRuleBasedDamagerRepairer
  implements IPresentationDamager, IPresentationRepairer {

  /**
   * The document this object works on.
   */
  private BytecodeDocument my_doc;

  /**
   * The default text attribute used for the colouring of all the areas governed
   * by the current object.
   */
  private TextAttribute my_dflt_textattribute;

  /**
   * Constructor for NonRuleBasedDamagerRepairer. It only caches the default
   * text attribute.
   *
   * @param a_default_text_attribute the default text attribute to be used
   *   by the current object
   */
  public NonRuleBasedDamagerRepairer(
        /*@ non_null @*/ final TextAttribute a_default_text_attribute) {
    my_dflt_textattribute = a_default_text_attribute;
  }

  /**
   * Associates the given document with the current damager-repairer.
   *
   * @param a_doc a document to associate with the current damager-repairer.
   * @see IPresentationRepairer#setDocument(IDocument)
   */
  public final void setDocument(final IDocument a_doc) {
    my_doc = (BytecodeDocument)a_doc;
  }

  /**
   * Returns the end offset of the line that contains the specified offset or
   * if the offset is inside a line delimiter, the end offset of the next line.
   *
   * @param an_offset the offset whose line end offset must be computed
   * @return the line end offset for the given offset
   * @throws UmbraLocationException if the offset is invalid in the current
   *    document
   */
  protected final int endOfLineOf(final int an_offset)
    throws UmbraLocationException {
    IRegion info;
    final int line;
    try {
      info = my_doc.getLineInformationOfOffset(an_offset);
      if (an_offset <= info.getOffset() + info.getLength())
        return info.getOffset() + info.getLength();

      line = my_doc.getLineOfOffset(an_offset);
    } catch (BadLocationException e) {
      throw new UmbraLocationException(true, an_offset, false);
    }
    try {
      info = my_doc.getLineInformation(line + 1);
      return info.getOffset() + info.getLength();
    } catch (BadLocationException e) {
      return my_doc.getLength();
    }
  }

  /**
   * Returns the damage in the document's presentation caused by the current
   * document change. In case the partitioning changed <code>a_partition</code>
   * is returned. In case the partitioning is unchanged the region is calculated
   * which starts with the beginning of the line in which the modification
   * started and ends with the end of the last line in which the modification
   * occurred. The region is always included in the given damaged region so
   * we have to check for cases in which the region starts/ends in the middle
   * of a line.
   *
   * @param a_partition a region which is damaged
   * @param an_event the event which changes the document
   * @param a_doc_partitioning_chngd <code>true</code> when the change changed
   *   document's partitioning
   * @return a new partition
   * @see IPresentationDamager#getDamageRegion(ITypedRegion, DocumentEvent,
   *                                           boolean)
   */
  public final IRegion getDamageRegion(final ITypedRegion a_partition,
                                       final DocumentEvent an_event,
                                       final boolean a_doc_partitioning_chngd) {
    if (!a_doc_partitioning_chngd) {
      try {
        final IRegion line_info =
          my_doc.getLineInformationOfOffset(an_event.getOffset());
        final int start = Math.max(a_partition.getOffset(),
                                   line_info.getOffset());
        int end =
          an_event.getOffset() + (an_event.getText() == null ?
                                         an_event.getLength() :
                                         an_event.getText().length());

        if (line_info.getOffset() <= end &&
            end <= line_info.getOffset() + line_info.getLength()) {
          // optimize the case of the same line
          end = line_info.getOffset() + line_info.getLength();
        } else {
          try {
            end = endOfLineOf(end);
          } catch (UmbraLocationException e) {
            GUIMessages.messageWrongLocation(
                         my_doc.getEditor().getSite().getShell(),
                         GUIMessages.BYTECODE_MESSAGE_TITLE, e);
          }
        }
        end = Math.min(
            a_partition.getOffset() + a_partition.getLength(),
            end);
        return new Region(start, end - start);
      } catch (BadLocationException e) {
        GUIMessages.messageWrongLocation(
                       my_doc.getEditor().getSite().getShell(),
                       GUIMessages.BYTECODE_MESSAGE_TITLE,
                       new UmbraLocationException(true, an_event.getOffset(),
                                                  false));
      }
    }
    return a_partition;
  }

  /**
   * This method adds to <code>a_presentation</code> a presentation style
   * to be used to display <code>a_region</code>. The presentation style
   * is defined with the use of the default attribute.
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
      my_dflt_textattribute);
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
