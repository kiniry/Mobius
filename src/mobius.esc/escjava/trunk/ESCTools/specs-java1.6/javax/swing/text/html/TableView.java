package javax.swing.text.html;

import java.awt.*;
import java.util.BitSet;
import java.util.Vector;
import java.util.Arrays;
import javax.swing.SizeRequirements;
import javax.swing.event.DocumentEvent;
import javax.swing.text.*;

class TableView extends BoxView implements ViewFactory {
    
    /*synthetic*/ static BitSet access$400() {
        return EMPTY;
    }
    
    /*synthetic*/ static boolean access$300(TableView x0) {
        return x0.multiRowCells;
    }
    
    /*synthetic*/ static int access$200(TableView x0) {
        return x0.cellSpacing;
    }
    
    /*synthetic*/ static int access$100(TableView x0) {
        return x0.borderWidth;
    }
    
    /*synthetic*/ static boolean access$000(TableView x0) {
        return x0.relativeCells;
    }
    
    public TableView(Element elem) {
        super(elem, View.Y_AXIS);
        rows = new Vector();
        gridValid = false;
        captionIndex = -1;
        totalColumnRequirements = new SizeRequirements();
    }
    
    protected TableView$RowView createTableRow(Element elem) {
        Object o = elem.getAttributes().getAttribute(StyleConstants.NameAttribute);
        if (o == HTML$Tag.TR) {
            return new TableView$RowView(this, elem);
        }
        return null;
    }
    
    public int getColumnCount() {
        return columnSpans.length;
    }
    
    public int getColumnSpan(int col) {
        if (col < columnSpans.length) {
            return columnSpans[col];
        }
        return 0;
    }
    
    public int getRowCount() {
        return rows.size();
    }
    
    public int getMultiRowSpan(int row0, int row1) {
        TableView$RowView rv0 = getRow(row0);
        TableView$RowView rv1 = getRow(row1);
        if ((rv0 != null) && (rv1 != null)) {
            int index0 = rv0.viewIndex;
            int index1 = rv1.viewIndex;
            int span = getOffset(Y_AXIS, index1) - getOffset(Y_AXIS, index0) + getSpan(Y_AXIS, index1);
            return span;
        }
        return 0;
    }
    
    public int getRowSpan(int row) {
        TableView$RowView rv = getRow(row);
        if (rv != null) {
            return getSpan(Y_AXIS, rv.viewIndex);
        }
        return 0;
    }
    
    TableView$RowView getRow(int row) {
        if (row < rows.size()) {
            return (TableView$RowView)(TableView$RowView)rows.elementAt(row);
        }
        return null;
    }
    
    protected View getViewAtPoint(int x, int y, Rectangle alloc) {
        int n = getViewCount();
        View v = null;
        Rectangle allocation = new Rectangle();
        for (int i = 0; i < n; i++) {
            allocation.setBounds(alloc);
            childAllocation(i, allocation);
            v = getView(i);
            if (v instanceof TableView$RowView) {
                v = ((TableView$RowView)(TableView$RowView)v).findViewAtPoint(x, y, allocation);
                if (v != null) {
                    alloc.setBounds(allocation);
                    return v;
                }
            }
        }
        return super.getViewAtPoint(x, y, alloc);
    }
    
    protected int getColumnsOccupied(View v) {
        AttributeSet a = v.getElement().getAttributes();
        if (a.isDefined(HTML$Attribute.COLSPAN)) {
            String s = (String)(String)a.getAttribute(HTML$Attribute.COLSPAN);
            if (s != null) {
                try {
                    return Integer.parseInt(s);
                } catch (NumberFormatException nfe) {
                }
            }
        }
        return 1;
    }
    
    protected int getRowsOccupied(View v) {
        AttributeSet a = v.getElement().getAttributes();
        if (a.isDefined(HTML$Attribute.ROWSPAN)) {
            String s = (String)(String)a.getAttribute(HTML$Attribute.ROWSPAN);
            if (s != null) {
                try {
                    return Integer.parseInt(s);
                } catch (NumberFormatException nfe) {
                }
            }
        }
        return 1;
    }
    
    protected void invalidateGrid() {
        gridValid = false;
    }
    
    protected StyleSheet getStyleSheet() {
        HTMLDocument doc = (HTMLDocument)(HTMLDocument)getDocument();
        return doc.getStyleSheet();
    }
    
    void updateInsets() {
        short top = (short)painter.getInset(TOP, this);
        short bottom = (short)painter.getInset(BOTTOM, this);
        if (captionIndex != -1) {
            View caption = getView(captionIndex);
            short h = (short)caption.getPreferredSpan(Y_AXIS);
            AttributeSet a = caption.getAttributes();
            Object align = a.getAttribute(CSS$Attribute.CAPTION_SIDE);
            if ((align != null) && (align.equals("bottom"))) {
                bottom += h;
            } else {
                top += h;
            }
        }
        setInsets(top, (short)painter.getInset(LEFT, this), bottom, (short)painter.getInset(RIGHT, this));
    }
    
    protected void setPropertiesFromAttributes() {
        StyleSheet sheet = getStyleSheet();
        attr = sheet.getViewAttributes(this);
        painter = sheet.getBoxPainter(attr);
        if (attr != null) {
            setInsets((short)painter.getInset(TOP, this), (short)painter.getInset(LEFT, this), (short)painter.getInset(BOTTOM, this), (short)painter.getInset(RIGHT, this));
            CSS$LengthValue lv = (CSS$LengthValue)(CSS$LengthValue)attr.getAttribute(CSS$Attribute.BORDER_SPACING);
            if (lv != null) {
                cellSpacing = (int)lv.getValue();
            } else {
                cellSpacing = 0;
            }
            lv = (CSS$LengthValue)(CSS$LengthValue)attr.getAttribute(CSS$Attribute.BORDER_TOP_WIDTH);
            if (lv != null) {
                borderWidth = (int)lv.getValue();
            } else {
                borderWidth = 0;
            }
        }
    }
    
    void updateGrid() {
        if (!gridValid) {
            relativeCells = false;
            multiRowCells = false;
            captionIndex = -1;
            rows.removeAllElements();
            int n = getViewCount();
            for (int i = 0; i < n; i++) {
                View v = getView(i);
                if (v instanceof TableView$RowView) {
                    rows.addElement(v);
                    TableView$RowView rv = (TableView$RowView)(TableView$RowView)v;
                    rv.clearFilledColumns();
                    rv.rowIndex = rows.size() - 1;
                    rv.viewIndex = i;
                } else {
                    Object o = v.getElement().getAttributes().getAttribute(StyleConstants.NameAttribute);
                    if (o instanceof HTML$Tag) {
                        HTML$Tag kind = (HTML$Tag)(HTML$Tag)o;
                        if (kind == HTML$Tag.CAPTION) {
                            captionIndex = i;
                        }
                    }
                }
            }
            int maxColumns = 0;
            int nrows = rows.size();
            for (int row = 0; row < nrows; row++) {
                TableView$RowView rv = getRow(row);
                int col = 0;
                for (int cell = 0; cell < rv.getViewCount(); cell++, col++) {
                    View cv = rv.getView(cell);
                    if (!relativeCells) {
                        AttributeSet a = cv.getAttributes();
                        CSS$LengthValue lv = (CSS$LengthValue)(CSS$LengthValue)a.getAttribute(CSS$Attribute.WIDTH);
                        if ((lv != null) && (lv.isPercentage())) {
                            relativeCells = true;
                        }
                    }
                    for (; rv.isFilled(col); col++) ;
                    int rowSpan = getRowsOccupied(cv);
                    if (rowSpan > 1) {
                        multiRowCells = true;
                    }
                    int colSpan = getColumnsOccupied(cv);
                    if ((colSpan > 1) || (rowSpan > 1)) {
                        int rowLimit = row + rowSpan;
                        int colLimit = col + colSpan;
                        for (int i = row; i < rowLimit; i++) {
                            for (int j = col; j < colLimit; j++) {
                                if (i != row || j != col) {
                                    addFill(i, j);
                                }
                            }
                        }
                        if (colSpan > 1) {
                            col += colSpan - 1;
                        }
                    }
                }
                maxColumns = Math.max(maxColumns, col);
            }
            columnSpans = new int[maxColumns];
            columnOffsets = new int[maxColumns];
            columnRequirements = new SizeRequirements[maxColumns];
            for (int i = 0; i < maxColumns; i++) {
                columnRequirements[i] = new SizeRequirements();
                columnRequirements[i].maximum = Integer.MAX_VALUE;
            }
            gridValid = true;
        }
    }
    
    void addFill(int row, int col) {
        TableView$RowView rv = getRow(row);
        if (rv != null) {
            rv.fillColumn(col);
        }
    }
    
    protected void layoutColumns(int targetSpan, int[] offsets, int[] spans, SizeRequirements[] reqs) {
        Arrays.fill(offsets, 0);
        Arrays.fill(spans, 0);
        colIterator.setLayoutArrays(offsets, spans, targetSpan);
        CSS.calculateTiledLayout(colIterator, targetSpan);
    }
    
    void calculateColumnRequirements(int axis) {
        for (SizeRequirements[] arr$ = columnRequirements, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            SizeRequirements req = arr$[i$];
            {
                req.minimum = 0;
                req.preferred = 0;
                req.maximum = Integer.MAX_VALUE;
            }
        }
        Container host = getContainer();
        if (host != null) {
            if (host instanceof JTextComponent) {
                skipComments = !((JTextComponent)(JTextComponent)host).isEditable();
            } else {
                skipComments = true;
            }
        }
        boolean hasMultiColumn = false;
        int nrows = getRowCount();
        for (int i = 0; i < nrows; i++) {
            TableView$RowView row = getRow(i);
            int col = 0;
            int ncells = row.getViewCount();
            for (int cell = 0; cell < ncells; cell++) {
                View cv = row.getView(cell);
                if (skipComments && !(cv instanceof TableView$CellView)) {
                    continue;
                }
                for (; row.isFilled(col); col++) ;
                int rowSpan = getRowsOccupied(cv);
                int colSpan = getColumnsOccupied(cv);
                if (colSpan == 1) {
                    checkSingleColumnCell(axis, col, cv);
                } else {
                    hasMultiColumn = true;
                    col += colSpan - 1;
                }
                col++;
            }
        }
        if (hasMultiColumn) {
            for (int i = 0; i < nrows; i++) {
                TableView$RowView row = getRow(i);
                int col = 0;
                int ncells = row.getViewCount();
                for (int cell = 0; cell < ncells; cell++) {
                    View cv = row.getView(cell);
                    if (skipComments && !(cv instanceof TableView$CellView)) {
                        continue;
                    }
                    for (; row.isFilled(col); col++) ;
                    int colSpan = getColumnsOccupied(cv);
                    if (colSpan > 1) {
                        checkMultiColumnCell(axis, col, colSpan, cv);
                        col += colSpan - 1;
                    }
                    col++;
                }
            }
        }
    }
    
    void checkSingleColumnCell(int axis, int col, View v) {
        SizeRequirements req = columnRequirements[col];
        req.minimum = Math.max((int)v.getMinimumSpan(axis), req.minimum);
        req.preferred = Math.max((int)v.getPreferredSpan(axis), req.preferred);
    }
    
    void checkMultiColumnCell(int axis, int col, int ncols, View v) {
        long min = 0;
        long pref = 0;
        long max = 0;
        for (int i = 0; i < ncols; i++) {
            SizeRequirements req = columnRequirements[col + i];
            min += req.minimum;
            pref += req.preferred;
            max += req.maximum;
        }
        int cmin = (int)v.getMinimumSpan(axis);
        if (cmin > min) {
            SizeRequirements[] reqs = new SizeRequirements[ncols];
            for (int i = 0; i < ncols; i++) {
                reqs[i] = columnRequirements[col + i];
            }
            int[] spans = new int[ncols];
            int[] offsets = new int[ncols];
            SizeRequirements.calculateTiledPositions(cmin, null, reqs, offsets, spans);
            for (int i = 0; i < ncols; i++) {
                SizeRequirements req = reqs[i];
                req.minimum = Math.max(spans[i], req.minimum);
                req.preferred = Math.max(req.minimum, req.preferred);
                req.maximum = Math.max(req.preferred, req.maximum);
            }
        }
        int cpref = (int)v.getPreferredSpan(axis);
        if (cpref > pref) {
            SizeRequirements[] reqs = new SizeRequirements[ncols];
            for (int i = 0; i < ncols; i++) {
                reqs[i] = columnRequirements[col + i];
            }
            int[] spans = new int[ncols];
            int[] offsets = new int[ncols];
            SizeRequirements.calculateTiledPositions(cpref, null, reqs, offsets, spans);
            for (int i = 0; i < ncols; i++) {
                SizeRequirements req = reqs[i];
                req.preferred = Math.max(spans[i], req.preferred);
                req.maximum = Math.max(req.preferred, req.maximum);
            }
        }
    }
    
    protected SizeRequirements calculateMinorAxisRequirements(int axis, SizeRequirements r) {
        updateGrid();
        calculateColumnRequirements(axis);
        if (r == null) {
            r = new SizeRequirements();
        }
        long min = 0;
        long pref = 0;
        int n = columnRequirements.length;
        for (int i = 0; i < n; i++) {
            SizeRequirements req = columnRequirements[i];
            min += req.minimum;
            pref += req.preferred;
        }
        int adjust = (n + 1) * cellSpacing + 2 * borderWidth;
        min += adjust;
        pref += adjust;
        r.minimum = (int)min;
        r.preferred = (int)pref;
        r.maximum = (int)pref;
        AttributeSet attr = getAttributes();
        CSS$LengthValue cssWidth = (CSS$LengthValue)(CSS$LengthValue)attr.getAttribute(CSS$Attribute.WIDTH);
        if (BlockView.spanSetFromAttributes(axis, r, cssWidth, null)) {
            if (r.minimum < (int)min) {
                r.maximum = r.minimum = r.preferred = (int)min;
            }
        }
        totalColumnRequirements.minimum = r.minimum;
        totalColumnRequirements.preferred = r.preferred;
        totalColumnRequirements.maximum = r.maximum;
        Object o = attr.getAttribute(CSS$Attribute.TEXT_ALIGN);
        if (o != null) {
            String ta = o.toString();
            if (ta.equals("left")) {
                r.alignment = 0;
            } else if (ta.equals("center")) {
                r.alignment = 0.5F;
            } else if (ta.equals("right")) {
                r.alignment = 1;
            } else {
                r.alignment = 0;
            }
        } else {
            r.alignment = 0;
        }
        return r;
    }
    
    protected SizeRequirements calculateMajorAxisRequirements(int axis, SizeRequirements r) {
        updateInsets();
        rowIterator.updateAdjustments();
        r = CSS.calculateTiledRequirements(rowIterator, r);
        r.maximum = r.preferred;
        return r;
    }
    
    protected void layoutMinorAxis(int targetSpan, int axis, int[] offsets, int[] spans) {
        updateGrid();
        int n = getRowCount();
        for (int i = 0; i < n; i++) {
            TableView$RowView row = getRow(i);
            row.layoutChanged(axis);
        }
        layoutColumns(targetSpan, columnOffsets, columnSpans, columnRequirements);
        super.layoutMinorAxis(targetSpan, axis, offsets, spans);
    }
    
    protected void layoutMajorAxis(int targetSpan, int axis, int[] offsets, int[] spans) {
        rowIterator.setLayoutArrays(offsets, spans);
        CSS.calculateTiledLayout(rowIterator, targetSpan);
        if (captionIndex != -1) {
            View caption = getView(captionIndex);
            int h = (int)caption.getPreferredSpan(Y_AXIS);
            spans[captionIndex] = h;
            short boxBottom = (short)painter.getInset(BOTTOM, this);
            if (boxBottom != getBottomInset()) {
                offsets[captionIndex] = targetSpan + boxBottom;
            } else {
                offsets[captionIndex] = -getTopInset();
            }
        }
    }
    
    protected View getViewAtPosition(int pos, Rectangle a) {
        int n = getViewCount();
        for (int i = 0; i < n; i++) {
            View v = getView(i);
            int p0 = v.getStartOffset();
            int p1 = v.getEndOffset();
            if ((pos >= p0) && (pos < p1)) {
                if (a != null) {
                    childAllocation(i, a);
                }
                return v;
            }
        }
        if (pos == getEndOffset()) {
            View v = getView(n - 1);
            if (a != null) {
                this.childAllocation(n - 1, a);
            }
            return v;
        }
        return null;
    }
    
    public AttributeSet getAttributes() {
        if (attr == null) {
            StyleSheet sheet = getStyleSheet();
            attr = sheet.getViewAttributes(this);
        }
        return attr;
    }
    
    public void paint(Graphics g, Shape allocation) {
        Rectangle a = allocation.getBounds();
        setSize(a.width, a.height);
        if (captionIndex != -1) {
            short top = (short)painter.getInset(TOP, this);
            short bottom = (short)painter.getInset(BOTTOM, this);
            if (top != getTopInset()) {
                int h = getTopInset() - top;
                a.y += h;
                a.height -= h;
            } else {
                a.height -= getBottomInset() - bottom;
            }
        }
        for (int i = borderWidth; i > 0; i--) {
            painter.paint(g, a.x + i, a.y + i, a.width - 2 * i, a.height - 2 * i, this);
        }
        int n = getViewCount();
        for (int i = 0; i < n; i++) {
            View v = getView(i);
            v.paint(g, getChildAllocation(i, allocation));
        }
    }
    
    public void setParent(View parent) {
        super.setParent(parent);
        if (parent != null) {
            setPropertiesFromAttributes();
        }
    }
    
    public ViewFactory getViewFactory() {
        return this;
    }
    
    public void insertUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        super.insertUpdate(e, a, this);
    }
    
    public void removeUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        super.removeUpdate(e, a, this);
    }
    
    public void changedUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        super.changedUpdate(e, a, this);
    }
    
    protected void forwardUpdate(DocumentEvent$ElementChange ec, DocumentEvent e, Shape a, ViewFactory f) {
        super.forwardUpdate(ec, e, a, f);
        if (a != null) {
            Component c = getContainer();
            if (c != null) {
                Rectangle alloc = (a instanceof Rectangle) ? (Rectangle)(Rectangle)a : a.getBounds();
                c.repaint(alloc.x, alloc.y, alloc.width, alloc.height);
            }
        }
    }
    
    public void replace(int offset, int length, View[] views) {
        super.replace(offset, length, views);
        invalidateGrid();
    }
    
    public View create(Element elem) {
        Object o = elem.getAttributes().getAttribute(StyleConstants.NameAttribute);
        if (o instanceof HTML$Tag) {
            HTML$Tag kind = (HTML$Tag)(HTML$Tag)o;
            if (kind == HTML$Tag.TR) {
                return createTableRow(elem);
            } else if ((kind == HTML$Tag.TD) || (kind == HTML$Tag.TH)) {
                return new TableView$CellView(this, elem);
            } else if (kind == HTML$Tag.CAPTION) {
                return new javax.swing.text.html.ParagraphView(elem);
            }
        }
        View p = getParent();
        if (p != null) {
            ViewFactory f = p.getViewFactory();
            if (f != null) {
                return f.create(elem);
            }
        }
        return null;
    }
    private AttributeSet attr;
    private StyleSheet$BoxPainter painter;
    private int cellSpacing;
    private int borderWidth;
    private int captionIndex;
    private boolean relativeCells;
    private boolean multiRowCells;
    int[] columnSpans;
    int[] columnOffsets;
    SizeRequirements totalColumnRequirements;
    SizeRequirements[] columnRequirements;
    TableView$RowIterator rowIterator = new TableView$RowIterator(this);
    TableView$ColumnIterator colIterator = new TableView$ColumnIterator(this);
    Vector rows;
    boolean skipComments = false;
    boolean gridValid;
    private static final BitSet EMPTY = new BitSet();
    {
    }
    {
    }
    {
    }
    {
    }
}
