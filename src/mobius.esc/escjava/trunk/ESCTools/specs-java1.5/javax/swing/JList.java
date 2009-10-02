package javax.swing;

import java.awt.event.*;
import java.awt.*;
import java.util.Vector;
import java.beans.*;
import javax.swing.event.*;
import javax.accessibility.*;
import javax.swing.plaf.*;
import java.io.ObjectOutputStream;
import java.io.IOException;

public class JList extends JComponent implements Scrollable, Accessible {
    
    /*synthetic*/ static ListSelectionModel access$100(JList x0) {
        return x0.selectionModel;
    }
    private static final String uiClassID = "ListUI";
    public static final int VERTICAL = 0;
    public static final int VERTICAL_WRAP = 1;
    public static final int HORIZONTAL_WRAP = 2;
    private int fixedCellWidth = -1;
    private int fixedCellHeight = -1;
    private int horizontalScrollIncrement = -1;
    private Object prototypeCellValue;
    private int visibleRowCount = 8;
    private Color selectionForeground;
    private Color selectionBackground;
    private boolean dragEnabled;
    private ListSelectionModel selectionModel;
    private ListModel dataModel;
    private ListCellRenderer cellRenderer;
    private ListSelectionListener selectionListener;
    private int layoutOrientation;
    
    public JList(ListModel dataModel) {
        
        if (dataModel == null) {
            throw new IllegalArgumentException("dataModel must be non null");
        }
        ToolTipManager toolTipManager = ToolTipManager.sharedInstance();
        toolTipManager.registerComponent(this);
        layoutOrientation = VERTICAL;
        this.dataModel = dataModel;
        selectionModel = createSelectionModel();
        setAutoscrolls(true);
        setOpaque(true);
        updateUI();
    }
    
    public JList(final Object[] listData) {
        this(new JList$1(listData));
    }
    
    public JList(final Vector listData) {
        this(new JList$2(listData));
    }
    
    public JList() {
        this(new JList$3());
    }
    
    public ListUI getUI() {
        return (ListUI)(ListUI)ui;
    }
    
    public void setUI(ListUI ui) {
        super.setUI(ui);
    }
    
    public void updateUI() {
        setUI((ListUI)(ListUI)UIManager.getUI(this));
        invalidate();
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    private void updateFixedCellSize() {
        ListCellRenderer cr = getCellRenderer();
        Object value = getPrototypeCellValue();
        if ((cr != null) && (value != null)) {
            Component c = cr.getListCellRendererComponent(this, value, 0, false, false);
            Font f = c.getFont();
            c.setFont(getFont());
            Dimension d = c.getPreferredSize();
            fixedCellWidth = d.width;
            fixedCellHeight = d.height;
            c.setFont(f);
        }
    }
    
    public Object getPrototypeCellValue() {
        return prototypeCellValue;
    }
    
    public void setPrototypeCellValue(Object prototypeCellValue) {
        Object oldValue = this.prototypeCellValue;
        this.prototypeCellValue = prototypeCellValue;
        if ((prototypeCellValue != null) && !prototypeCellValue.equals(oldValue)) {
            updateFixedCellSize();
        }
        firePropertyChange("prototypeCellValue", oldValue, prototypeCellValue);
    }
    
    public int getFixedCellWidth() {
        return fixedCellWidth;
    }
    
    public void setFixedCellWidth(int width) {
        int oldValue = fixedCellWidth;
        fixedCellWidth = width;
        firePropertyChange("fixedCellWidth", oldValue, fixedCellWidth);
    }
    
    public int getFixedCellHeight() {
        return fixedCellHeight;
    }
    
    public void setFixedCellHeight(int height) {
        int oldValue = fixedCellHeight;
        fixedCellHeight = height;
        firePropertyChange("fixedCellHeight", oldValue, fixedCellHeight);
    }
    
    public ListCellRenderer getCellRenderer() {
        return cellRenderer;
    }
    
    public void setCellRenderer(ListCellRenderer cellRenderer) {
        ListCellRenderer oldValue = this.cellRenderer;
        this.cellRenderer = cellRenderer;
        if ((cellRenderer != null) && !cellRenderer.equals(oldValue)) {
            updateFixedCellSize();
        }
        firePropertyChange("cellRenderer", oldValue, cellRenderer);
    }
    
    public Color getSelectionForeground() {
        return selectionForeground;
    }
    
    public void setSelectionForeground(Color selectionForeground) {
        Color oldValue = this.selectionForeground;
        this.selectionForeground = selectionForeground;
        firePropertyChange("selectionForeground", oldValue, selectionForeground);
    }
    
    public Color getSelectionBackground() {
        return selectionBackground;
    }
    
    public void setSelectionBackground(Color selectionBackground) {
        Color oldValue = this.selectionBackground;
        this.selectionBackground = selectionBackground;
        firePropertyChange("selectionBackground", oldValue, selectionBackground);
    }
    
    public int getVisibleRowCount() {
        return visibleRowCount;
    }
    
    public void setVisibleRowCount(int visibleRowCount) {
        int oldValue = this.visibleRowCount;
        this.visibleRowCount = Math.max(0, visibleRowCount);
        firePropertyChange("visibleRowCount", oldValue, visibleRowCount);
    }
    
    public int getLayoutOrientation() {
        return layoutOrientation;
    }
    
    public void setLayoutOrientation(int layoutOrientation) {
        int oldValue = this.layoutOrientation;
        switch (layoutOrientation) {
        case VERTICAL: 
        
        case VERTICAL_WRAP: 
        
        case HORIZONTAL_WRAP: 
            this.layoutOrientation = layoutOrientation;
            firePropertyChange("layoutOrientation", oldValue, layoutOrientation);
            break;
        
        default: 
            throw new IllegalArgumentException("layoutOrientation must be one of: VERTICAL, HORIZONTAL_WRAP or VERTICAL_WRAP");
        
        }
    }
    
    public int getFirstVisibleIndex() {
        Rectangle r = getVisibleRect();
        int first;
        if (this.getComponentOrientation().isLeftToRight()) {
            first = locationToIndex(r.getLocation());
        } else {
            first = locationToIndex(new Point((r.x + r.width) - 1, r.y));
        }
        if (first != -1) {
            Rectangle bounds = getCellBounds(first, first);
            if (bounds != null) {
                SwingUtilities.computeIntersection(r.x, r.y, r.width, r.height, bounds);
                if (bounds.width == 0 || bounds.height == 0) {
                    first = -1;
                }
            }
        }
        return first;
    }
    
    public int getLastVisibleIndex() {
        boolean leftToRight = this.getComponentOrientation().isLeftToRight();
        Rectangle r = getVisibleRect();
        Point lastPoint;
        if (leftToRight) {
            lastPoint = new Point((r.x + r.width) - 1, (r.y + r.height) - 1);
        } else {
            lastPoint = new Point(r.x, (r.y + r.height) - 1);
        }
        int location = locationToIndex(lastPoint);
        if (location != -1) {
            Rectangle bounds = getCellBounds(location, location);
            if (bounds != null) {
                SwingUtilities.computeIntersection(r.x, r.y, r.width, r.height, bounds);
                if (bounds.width == 0 || bounds.height == 0) {
                    Point visibleLL = new Point(r.x, lastPoint.y);
                    int last;
                    int llIndex = -1;
                    int lrIndex = location;
                    location = -1;
                    do {
                        last = llIndex;
                        llIndex = locationToIndex(visibleLL);
                        if (llIndex != -1) {
                            bounds = getCellBounds(llIndex, llIndex);
                            if (llIndex != lrIndex && bounds != null && bounds.contains(visibleLL)) {
                                location = llIndex;
                                visibleLL.x = bounds.x + bounds.width + 1;
                                if (visibleLL.x >= lastPoint.x) {
                                    last = llIndex;
                                }
                            } else {
                                last = llIndex;
                            }
                        }
                    }                     while (llIndex != -1 && last != llIndex);
                }
            }
        }
        return location;
    }
    
    public void ensureIndexIsVisible(int index) {
        Rectangle cellBounds = getCellBounds(index, index);
        if (cellBounds != null) {
            scrollRectToVisible(cellBounds);
        }
    }
    
    public void setDragEnabled(boolean b) {
        if (b && GraphicsEnvironment.isHeadless()) {
            throw new HeadlessException();
        }
        dragEnabled = b;
    }
    
    public boolean getDragEnabled() {
        return dragEnabled;
    }
    
    public int getNextMatch(String prefix, int startIndex, Position$Bias bias) {
        ListModel model = getModel();
        int max = model.getSize();
        if (prefix == null) {
            throw new IllegalArgumentException();
        }
        if (startIndex < 0 || startIndex >= max) {
            throw new IllegalArgumentException();
        }
        prefix = prefix.toUpperCase();
        int increment = (bias == Position$Bias.Forward) ? 1 : -1;
        int index = startIndex;
        do {
            Object o = model.getElementAt(index);
            if (o != null) {
                String string;
                if (o instanceof String) {
                    string = ((String)(String)o).toUpperCase();
                } else {
                    string = o.toString();
                    if (string != null) {
                        string = string.toUpperCase();
                    }
                }
                if (string != null && string.startsWith(prefix)) {
                    return index;
                }
            }
            index = (index + increment + max) % max;
        }         while (index != startIndex);
        return -1;
    }
    
    public String getToolTipText(MouseEvent event) {
        if (event != null) {
            Point p = event.getPoint();
            int index = locationToIndex(p);
            ListCellRenderer r = getCellRenderer();
            Rectangle cellBounds;
            if (index != -1 && r != null && (cellBounds = getCellBounds(index, index)) != null && cellBounds.contains(p.x, p.y)) {
                ListSelectionModel lsm = getSelectionModel();
                Component rComponent = r.getListCellRendererComponent(this, getModel().getElementAt(index), index, lsm.isSelectedIndex(index), (hasFocus() && (lsm.getLeadSelectionIndex() == index)));
                if (rComponent instanceof JComponent) {
                    MouseEvent newEvent;
                    p.translate(-cellBounds.x, -cellBounds.y);
                    newEvent = new MouseEvent(rComponent, event.getID(), event.getWhen(), event.getModifiers(), p.x, p.y, event.getClickCount(), event.isPopupTrigger());
                    String tip = ((JComponent)(JComponent)rComponent).getToolTipText(newEvent);
                    if (tip != null) {
                        return tip;
                    }
                }
            }
        }
        return super.getToolTipText();
    }
    
    public int locationToIndex(Point location) {
        ListUI ui = getUI();
        return (ui != null) ? ui.locationToIndex(this, location) : -1;
    }
    
    public Point indexToLocation(int index) {
        ListUI ui = getUI();
        return (ui != null) ? ui.indexToLocation(this, index) : null;
    }
    
    public Rectangle getCellBounds(int index0, int index1) {
        ListUI ui = getUI();
        return (ui != null) ? ui.getCellBounds(this, index0, index1) : null;
    }
    
    public ListModel getModel() {
        return dataModel;
    }
    
    public void setModel(ListModel model) {
        if (model == null) {
            throw new IllegalArgumentException("model must be non null");
        }
        ListModel oldValue = dataModel;
        dataModel = model;
        firePropertyChange("model", oldValue, dataModel);
        clearSelection();
    }
    
    public void setListData(final Object[] listData) {
        setModel(new JList$4(this, listData));
    }
    
    public void setListData(final Vector listData) {
        setModel(new JList$5(this, listData));
    }
    
    protected ListSelectionModel createSelectionModel() {
        return new DefaultListSelectionModel();
    }
    
    public ListSelectionModel getSelectionModel() {
        return selectionModel;
    }
    
    protected void fireSelectionValueChanged(int firstIndex, int lastIndex, boolean isAdjusting) {
        Object[] listeners = listenerList.getListenerList();
        ListSelectionEvent e = null;
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == ListSelectionListener.class) {
                if (e == null) {
                    e = new ListSelectionEvent(this, firstIndex, lastIndex, isAdjusting);
                }
                ((ListSelectionListener)(ListSelectionListener)listeners[i + 1]).valueChanged(e);
            }
        }
    }
    {
    }
    
    public void addListSelectionListener(ListSelectionListener listener) {
        if (selectionListener == null) {
            selectionListener = new JList$ListSelectionHandler(this, null);
            getSelectionModel().addListSelectionListener(selectionListener);
        }
        listenerList.add(ListSelectionListener.class, listener);
    }
    
    public void removeListSelectionListener(ListSelectionListener listener) {
        listenerList.remove(ListSelectionListener.class, listener);
    }
    
    public ListSelectionListener[] getListSelectionListeners() {
        return (ListSelectionListener[])(ListSelectionListener[])listenerList.getListeners(ListSelectionListener.class);
    }
    
    public void setSelectionModel(ListSelectionModel selectionModel) {
        if (selectionModel == null) {
            throw new IllegalArgumentException("selectionModel must be non null");
        }
        if (selectionListener != null) {
            this.selectionModel.removeListSelectionListener(selectionListener);
            selectionModel.addListSelectionListener(selectionListener);
        }
        ListSelectionModel oldValue = this.selectionModel;
        this.selectionModel = selectionModel;
        firePropertyChange("selectionModel", oldValue, selectionModel);
    }
    
    public void setSelectionMode(int selectionMode) {
        getSelectionModel().setSelectionMode(selectionMode);
    }
    
    public int getSelectionMode() {
        return getSelectionModel().getSelectionMode();
    }
    
    public int getAnchorSelectionIndex() {
        return getSelectionModel().getAnchorSelectionIndex();
    }
    
    public int getLeadSelectionIndex() {
        return getSelectionModel().getLeadSelectionIndex();
    }
    
    public int getMinSelectionIndex() {
        return getSelectionModel().getMinSelectionIndex();
    }
    
    public int getMaxSelectionIndex() {
        return getSelectionModel().getMaxSelectionIndex();
    }
    
    public boolean isSelectedIndex(int index) {
        return getSelectionModel().isSelectedIndex(index);
    }
    
    public boolean isSelectionEmpty() {
        return getSelectionModel().isSelectionEmpty();
    }
    
    public void clearSelection() {
        getSelectionModel().clearSelection();
    }
    
    public void setSelectionInterval(int anchor, int lead) {
        getSelectionModel().setSelectionInterval(anchor, lead);
    }
    
    public void addSelectionInterval(int anchor, int lead) {
        getSelectionModel().addSelectionInterval(anchor, lead);
    }
    
    public void removeSelectionInterval(int index0, int index1) {
        getSelectionModel().removeSelectionInterval(index0, index1);
    }
    
    public void setValueIsAdjusting(boolean b) {
        getSelectionModel().setValueIsAdjusting(b);
    }
    
    public boolean getValueIsAdjusting() {
        return getSelectionModel().getValueIsAdjusting();
    }
    
    public int[] getSelectedIndices() {
        ListSelectionModel sm = getSelectionModel();
        int iMin = sm.getMinSelectionIndex();
        int iMax = sm.getMaxSelectionIndex();
        if ((iMin < 0) || (iMax < 0)) {
            return new int[0];
        }
        int[] rvTmp = new int[1 + (iMax - iMin)];
        int n = 0;
        for (int i = iMin; i <= iMax; i++) {
            if (sm.isSelectedIndex(i)) {
                rvTmp[n++] = i;
            }
        }
        int[] rv = new int[n];
        System.arraycopy(rvTmp, 0, rv, 0, n);
        return rv;
    }
    
    public void setSelectedIndex(int index) {
        if (index >= getModel().getSize()) {
            return;
        }
        getSelectionModel().setSelectionInterval(index, index);
    }
    
    public void setSelectedIndices(int[] indices) {
        ListSelectionModel sm = getSelectionModel();
        sm.clearSelection();
        int size = getModel().getSize();
        for (int i = 0; i < indices.length; i++) {
            if (indices[i] < size) {
                sm.addSelectionInterval(indices[i], indices[i]);
            }
        }
    }
    
    public Object[] getSelectedValues() {
        ListSelectionModel sm = getSelectionModel();
        ListModel dm = getModel();
        int iMin = sm.getMinSelectionIndex();
        int iMax = sm.getMaxSelectionIndex();
        if ((iMin < 0) || (iMax < 0)) {
            return new Object[0];
        }
        Object[] rvTmp = new Object[1 + (iMax - iMin)];
        int n = 0;
        for (int i = iMin; i <= iMax; i++) {
            if (sm.isSelectedIndex(i)) {
                rvTmp[n++] = dm.getElementAt(i);
            }
        }
        Object[] rv = new Object[n];
        System.arraycopy(rvTmp, 0, rv, 0, n);
        return rv;
    }
    
    public int getSelectedIndex() {
        return getMinSelectionIndex();
    }
    
    public Object getSelectedValue() {
        int i = getMinSelectionIndex();
        return (i == -1) ? null : getModel().getElementAt(i);
    }
    
    public void setSelectedValue(Object anObject, boolean shouldScroll) {
        if (anObject == null) setSelectedIndex(-1); else if (!anObject.equals(getSelectedValue())) {
            int i;
            int c;
            ListModel dm = getModel();
            for (i = 0, c = dm.getSize(); i < c; i++) if (anObject.equals(dm.getElementAt(i))) {
                setSelectedIndex(i);
                if (shouldScroll) ensureIndexIsVisible(i);
                repaint();
                return;
            }
            setSelectedIndex(-1);
        }
        repaint();
    }
    
    private void checkScrollableParameters(Rectangle visibleRect, int orientation) {
        if (visibleRect == null) {
            throw new IllegalArgumentException("visibleRect must be non-null");
        }
        switch (orientation) {
        case SwingConstants.VERTICAL: 
        
        case SwingConstants.HORIZONTAL: 
            break;
        
        default: 
            throw new IllegalArgumentException("orientation must be one of: VERTICAL, HORIZONTAL");
        
        }
    }
    
    public Dimension getPreferredScrollableViewportSize() {
        if (getLayoutOrientation() != VERTICAL) {
            return getPreferredSize();
        }
        Insets insets = getInsets();
        int dx = insets.left + insets.right;
        int dy = insets.top + insets.bottom;
        int visibleRowCount = getVisibleRowCount();
        int fixedCellWidth = getFixedCellWidth();
        int fixedCellHeight = getFixedCellHeight();
        if ((fixedCellWidth > 0) && (fixedCellHeight > 0)) {
            int width = fixedCellWidth + dx;
            int height = (visibleRowCount * fixedCellHeight) + dy;
            return new Dimension(width, height);
        } else if (getModel().getSize() > 0) {
            int width = getPreferredSize().width;
            int height;
            Rectangle r = getCellBounds(0, 0);
            if (r != null) {
                height = (visibleRowCount * r.height) + dy;
            } else {
                height = 1;
            }
            return new Dimension(width, height);
        } else {
            fixedCellWidth = (fixedCellWidth > 0) ? fixedCellWidth : 256;
            fixedCellHeight = (fixedCellHeight > 0) ? fixedCellHeight : 16;
            return new Dimension(fixedCellWidth, fixedCellHeight * visibleRowCount);
        }
    }
    
    public int getScrollableUnitIncrement(Rectangle visibleRect, int orientation, int direction) {
        checkScrollableParameters(visibleRect, orientation);
        if (orientation == SwingConstants.VERTICAL) {
            int row = getFirstVisibleIndex();
            if (row == -1) {
                return 0;
            } else {
                if (direction > 0) {
                    Rectangle r = getCellBounds(row, row);
                    return (r == null) ? 0 : r.height - (visibleRect.y - r.y);
                } else {
                    Rectangle r = getCellBounds(row, row);
                    if ((r.y == visibleRect.y) && (row == 0)) {
                        return 0;
                    } else if (r.y == visibleRect.y) {
                        Point loc = r.getLocation();
                        loc.y--;
                        int prevIndex = locationToIndex(loc);
                        Rectangle prevR = getCellBounds(prevIndex, prevIndex);
                        if (prevR == null || prevR.y >= r.y) {
                            return 0;
                        }
                        return prevR.height;
                    } else {
                        return visibleRect.y - r.y;
                    }
                }
            }
        } else if (orientation == SwingConstants.HORIZONTAL && getLayoutOrientation() != JList.VERTICAL) {
            int index = locationToIndex(visibleRect.getLocation());
            if (index != -1) {
                Rectangle cellBounds = getCellBounds(index, index);
                if (cellBounds != null) {
                    if (cellBounds.x != visibleRect.x) {
                        if (direction < 0) {
                            return Math.abs(cellBounds.x - visibleRect.x);
                        }
                        return cellBounds.width + cellBounds.x - visibleRect.x;
                    }
                    return cellBounds.width;
                }
            }
        }
        Font f = getFont();
        return (f != null) ? f.getSize() : 1;
    }
    
    public int getScrollableBlockIncrement(Rectangle visibleRect, int orientation, int direction) {
        checkScrollableParameters(visibleRect, orientation);
        if (orientation == SwingConstants.VERTICAL) {
            int inc = visibleRect.height;
            if (direction > 0) {
                int last = locationToIndex(new Point(visibleRect.x, visibleRect.y + visibleRect.height - 1));
                if (last != -1) {
                    Rectangle lastRect = getCellBounds(last, last);
                    if (lastRect != null) {
                        inc = lastRect.y - visibleRect.y;
                        if ((inc == 0) && (last < getModel().getSize() - 1)) {
                            inc = lastRect.height;
                        }
                    }
                }
            } else {
                int newFirst = locationToIndex(new Point(visibleRect.x, visibleRect.y - visibleRect.height));
                int first = getFirstVisibleIndex();
                if (newFirst != -1) {
                    if (first == -1) {
                        first = locationToIndex(visibleRect.getLocation());
                    }
                    Rectangle newFirstRect = getCellBounds(newFirst, newFirst);
                    Rectangle firstRect = getCellBounds(first, first);
                    if ((newFirstRect != null) && (firstRect != null)) {
                        while ((newFirstRect.y + visibleRect.height < firstRect.y + firstRect.height) && (newFirstRect.y < firstRect.y)) {
                            newFirst++;
                            newFirstRect = getCellBounds(newFirst, newFirst);
                        }
                        inc = visibleRect.y - newFirstRect.y;
                        if ((inc <= 0) && (newFirstRect.y > 0)) {
                            newFirst--;
                            newFirstRect = getCellBounds(newFirst, newFirst);
                            if (newFirstRect != null) {
                                inc = visibleRect.y - newFirstRect.y;
                            }
                        }
                    }
                }
            }
            return inc;
        } else if (orientation == SwingConstants.HORIZONTAL && getLayoutOrientation() != JList.VERTICAL) {
            int inc = visibleRect.width;
            if (direction > 0) {
                int last = locationToIndex(new Point(visibleRect.x + visibleRect.width - 1, visibleRect.y));
                if (last != -1) {
                    Rectangle lastRect = getCellBounds(last, last);
                    if (lastRect != null) {
                        inc = lastRect.x - visibleRect.x;
                        if (inc < 0) {
                            inc += lastRect.width;
                        } else if ((inc == 0) && (last < getModel().getSize() - 1)) {
                            inc = lastRect.width;
                        }
                    }
                }
            } else {
                int first = locationToIndex(new Point(visibleRect.x - visibleRect.width, visibleRect.y));
                if (first != -1) {
                    Rectangle firstRect = getCellBounds(first, first);
                    if (firstRect != null) {
                        if (firstRect.x < visibleRect.x - visibleRect.width) {
                            if (firstRect.x + firstRect.width >= visibleRect.x) {
                                inc = visibleRect.x - firstRect.x;
                            } else {
                                inc = visibleRect.x - firstRect.x - firstRect.width;
                            }
                        } else {
                            inc = visibleRect.x - firstRect.x;
                        }
                    }
                }
            }
            return inc;
        }
        return visibleRect.width;
    }
    
    public boolean getScrollableTracksViewportWidth() {
        if (getLayoutOrientation() == HORIZONTAL_WRAP && getVisibleRowCount() <= 0) {
            return true;
        }
        if (getParent() instanceof JViewport) {
            return (((JViewport)(JViewport)getParent()).getWidth() > getPreferredSize().width);
        }
        return false;
    }
    
    public boolean getScrollableTracksViewportHeight() {
        if (getLayoutOrientation() == VERTICAL_WRAP && getVisibleRowCount() <= 0) {
            return true;
        }
        if (getParent() instanceof JViewport) {
            return (((JViewport)(JViewport)getParent()).getHeight() > getPreferredSize().height);
        }
        return false;
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        if (getUIClassID().equals(uiClassID)) {
            byte count = JComponent.getWriteObjCounter(this);
            JComponent.setWriteObjCounter(this, --count);
            if (count == 0 && ui != null) {
                ui.installUI(this);
            }
        }
    }
    
    protected String paramString() {
        String selectionForegroundString = (selectionForeground != null ? selectionForeground.toString() : "");
        String selectionBackgroundString = (selectionBackground != null ? selectionBackground.toString() : "");
        return super.paramString() + ",fixedCellHeight=" + fixedCellHeight + ",fixedCellWidth=" + fixedCellWidth + ",horizontalScrollIncrement=" + horizontalScrollIncrement + ",selectionBackground=" + selectionBackgroundString + ",selectionForeground=" + selectionForegroundString + ",visibleRowCount=" + visibleRowCount + ",layoutOrientation=" + layoutOrientation;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JList$AccessibleJList(this);
        }
        return accessibleContext;
    }
    {
    }
}
