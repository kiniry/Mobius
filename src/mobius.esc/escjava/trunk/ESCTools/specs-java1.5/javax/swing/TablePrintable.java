package javax.swing;

import javax.swing.table.*;
import java.awt.*;
import java.awt.print.*;
import java.awt.geom.*;
import java.text.MessageFormat;

class TablePrintable implements Printable {
    /*synthetic*/ static final boolean $assertionsDisabled = !TablePrintable.class.desiredAssertionStatus();
    private JTable table;
    private JTableHeader header;
    private TableColumnModel colModel;
    private int totalColWidth;
    private JTable$PrintMode printMode;
    private MessageFormat headerFormat;
    private MessageFormat footerFormat;
    private int last = -1;
    private int row = 0;
    private int col = 0;
    private final Rectangle clip = new Rectangle(0, 0, 0, 0);
    private final Rectangle hclip = new Rectangle(0, 0, 0, 0);
    private final Rectangle tempRect = new Rectangle(0, 0, 0, 0);
    private static final int H_F_SPACE = 8;
    private static final float HEADER_FONT_SIZE = 18.0F;
    private static final float FOOTER_FONT_SIZE = 12.0F;
    private Font headerFont;
    private Font footerFont;
    
    public TablePrintable(JTable table, JTable$PrintMode printMode, MessageFormat headerFormat, MessageFormat footerFormat) {
        
        this.table = table;
        header = table.getTableHeader();
        colModel = table.getColumnModel();
        totalColWidth = colModel.getTotalColumnWidth();
        if (header != null) {
            hclip.height = header.getHeight();
        }
        this.printMode = printMode;
        this.headerFormat = headerFormat;
        this.footerFormat = footerFormat;
        headerFont = table.getFont().deriveFont(Font.BOLD, HEADER_FONT_SIZE);
        footerFont = table.getFont().deriveFont(Font.PLAIN, FOOTER_FONT_SIZE);
    }
    
    public int print(Graphics graphics, PageFormat pageFormat, int pageIndex) throws PrinterException {
        final int imgWidth = (int)pageFormat.getImageableWidth();
        final int imgHeight = (int)pageFormat.getImageableHeight();
        if (imgWidth <= 0) {
            throw new PrinterException("Width of printable area is too small.");
        }
        Object[] pageNumber = new Object[]{new Integer(pageIndex + 1)};
        String headerText = null;
        if (headerFormat != null) {
            headerText = headerFormat.format(pageNumber);
        }
        String footerText = null;
        if (footerFormat != null) {
            footerText = footerFormat.format(pageNumber);
        }
        Rectangle2D hRect = null;
        Rectangle2D fRect = null;
        int headerTextSpace = 0;
        int footerTextSpace = 0;
        int availableSpace = imgHeight;
        if (headerText != null) {
            graphics.setFont(headerFont);
            hRect = graphics.getFontMetrics().getStringBounds(headerText, graphics);
            headerTextSpace = (int)Math.ceil(hRect.getHeight());
            availableSpace -= headerTextSpace + H_F_SPACE;
        }
        if (footerText != null) {
            graphics.setFont(footerFont);
            fRect = graphics.getFontMetrics().getStringBounds(footerText, graphics);
            footerTextSpace = (int)Math.ceil(fRect.getHeight());
            availableSpace -= footerTextSpace + H_F_SPACE;
        }
        if (availableSpace <= 0) {
            throw new PrinterException("Height of printable area is too small.");
        }
        double sf = 1.0;
        if (printMode == JTable$PrintMode.FIT_WIDTH && totalColWidth > imgWidth) {
            if (!$assertionsDisabled && !(imgWidth > 0)) throw new AssertionError();
            if (!$assertionsDisabled && !(totalColWidth > 1)) throw new AssertionError();
            sf = (double)imgWidth / (double)totalColWidth;
        }
        if (!$assertionsDisabled && !(sf > 0)) throw new AssertionError();
        while (last < pageIndex) {
            if (row >= table.getRowCount() && col == 0) {
                return NO_SUCH_PAGE;
            }
            int scaledWidth = (int)(imgWidth / sf);
            int scaledHeight = (int)((availableSpace - hclip.height) / sf);
            findNextClip(scaledWidth, scaledHeight);
            last++;
        }
        Graphics2D g2d = (Graphics2D)(Graphics2D)graphics;
        g2d.translate(pageFormat.getImageableX(), pageFormat.getImageableY());
        AffineTransform oldTrans;
        if (footerText != null) {
            oldTrans = g2d.getTransform();
            g2d.translate(0, imgHeight - footerTextSpace);
            printText(g2d, footerText, fRect, footerFont, imgWidth);
            g2d.setTransform(oldTrans);
        }
        if (headerText != null) {
            printText(g2d, headerText, hRect, headerFont, imgWidth);
            g2d.translate(0, headerTextSpace + H_F_SPACE);
        }
        tempRect.x = 0;
        tempRect.y = 0;
        tempRect.width = imgWidth;
        tempRect.height = availableSpace;
        g2d.clip(tempRect);
        if (sf != 1.0) {
            g2d.scale(sf, sf);
        } else {
            int diff = (imgWidth - clip.width) / 2;
            g2d.translate(diff, 0);
        }
        oldTrans = g2d.getTransform();
        Shape oldClip = g2d.getClip();
        if (header != null) {
            hclip.x = clip.x;
            hclip.width = clip.width;
            g2d.translate(-hclip.x, 0);
            g2d.clip(hclip);
            header.print(g2d);
            g2d.setTransform(oldTrans);
            g2d.setClip(oldClip);
            g2d.translate(0, hclip.height);
        }
        g2d.translate(-clip.x, -clip.y);
        g2d.clip(clip);
        table.print(g2d);
        g2d.setTransform(oldTrans);
        g2d.setClip(oldClip);
        g2d.setColor(Color.BLACK);
        g2d.drawRect(0, 0, clip.width, hclip.height + clip.height);
        return PAGE_EXISTS;
    }
    
    private void printText(Graphics2D g2d, String text, Rectangle2D rect, Font font, int imgWidth) {
        int tx;
        if (rect.getWidth() < imgWidth) {
            tx = (int)((imgWidth - rect.getWidth()) / 2);
        } else if (table.getComponentOrientation().isLeftToRight()) {
            tx = 0;
        } else {
            tx = -(int)(Math.ceil(rect.getWidth()) - imgWidth);
        }
        int ty = (int)Math.ceil(Math.abs(rect.getY()));
        g2d.setColor(Color.BLACK);
        g2d.setFont(font);
        g2d.drawString(text, tx, ty);
    }
    
    private void findNextClip(int pw, int ph) {
        final boolean ltr = table.getComponentOrientation().isLeftToRight();
        if (col == 0) {
            if (ltr) {
                clip.x = 0;
            } else {
                clip.x = totalColWidth;
            }
            clip.y += clip.height;
            clip.width = 0;
            clip.height = 0;
            int rowCount = table.getRowCount();
            int rowHeight = table.getRowHeight(row);
            do {
                clip.height += rowHeight;
                if (++row >= rowCount) {
                    break;
                }
                rowHeight = table.getRowHeight(row);
            }             while (clip.height + rowHeight <= ph);
        }
        if (printMode == JTable$PrintMode.FIT_WIDTH) {
            clip.x = 0;
            clip.width = totalColWidth;
            return;
        }
        if (ltr) {
            clip.x += clip.width;
        }
        clip.width = 0;
        int colCount = table.getColumnCount();
        int colWidth = colModel.getColumn(col).getWidth();
        do {
            clip.width += colWidth;
            if (!ltr) {
                clip.x -= colWidth;
            }
            if (++col >= colCount) {
                col = 0;
                break;
            }
            colWidth = colModel.getColumn(col).getWidth();
        }         while (clip.width + colWidth <= pw);
    }
}
