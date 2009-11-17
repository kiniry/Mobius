package java.awt;

import java.util.Vector;
import java.util.EventListener;
import java.awt.peer.ListPeer;
import java.awt.event.*;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;
import javax.accessibility.*;

public class List extends Component implements ItemSelectable, Accessible {
    Vector items = new Vector();
    int rows = 0;
    boolean multipleMode = false;
    int[] selected = new int[0];
    int visibleIndex = -1;
    transient ActionListener actionListener;
    transient ItemListener itemListener;
    private static final String base = "list";
    private static int nameCounter = 0;
    private static final long serialVersionUID = -3304312411574666869L;
    
    public List() throws HeadlessException {
        this(0, false);
    }
    
    public List(int rows) throws HeadlessException {
        this(rows, false);
    }
    static final int DEFAULT_VISIBLE_ROWS = 4;
    
    public List(int rows, boolean multipleMode) throws HeadlessException {
        
        GraphicsEnvironment.checkHeadless();
        this.rows = (rows != 0) ? rows : DEFAULT_VISIBLE_ROWS;
        this.multipleMode = multipleMode;
    }
    
    String constructComponentName() {
        synchronized (getClass()) {
            return base + nameCounter++;
        }
    }
    
    public void addNotify() {
        synchronized (getTreeLock()) {
            if (peer == null) peer = getToolkit().createList(this);
            super.addNotify();
        }
    }
    
    public void removeNotify() {
        synchronized (getTreeLock()) {
            ListPeer peer = (ListPeer)(ListPeer)this.peer;
            if (peer != null) {
                selected = peer.getSelectedIndexes();
            }
            super.removeNotify();
        }
    }
    
    public int getItemCount() {
        return countItems();
    }
    
    
    public int countItems() {
        return items.size();
    }
    
    public String getItem(int index) {
        return getItemImpl(index);
    }
    
    final String getItemImpl(int index) {
        return (String)(String)items.elementAt(index);
    }
    
    public synchronized String[] getItems() {
        String[] itemCopies = new String[items.size()];
        items.copyInto(itemCopies);
        return itemCopies;
    }
    
    public void add(String item) {
        addItem(item);
    }
    
    
    public void addItem(String item) {
        addItem(item, -1);
    }
    
    public void add(String item, int index) {
        addItem(item, index);
    }
    
    
    public synchronized void addItem(String item, int index) {
        if (index < -1 || index >= items.size()) {
            index = -1;
        }
        if (item == null) {
            item = "";
        }
        if (index == -1) {
            items.addElement(item);
        } else {
            items.insertElementAt(item, index);
        }
        ListPeer peer = (ListPeer)(ListPeer)this.peer;
        if (peer != null) {
            peer.addItem(item, index);
        }
    }
    
    public synchronized void replaceItem(String newValue, int index) {
        remove(index);
        add(newValue, index);
    }
    
    public void removeAll() {
        clear();
    }
    
    
    public synchronized void clear() {
        ListPeer peer = (ListPeer)(ListPeer)this.peer;
        if (peer != null) {
            peer.clear();
        }
        items = new Vector();
        selected = new int[0];
    }
    
    public synchronized void remove(String item) {
        int index = items.indexOf(item);
        if (index < 0) {
            throw new IllegalArgumentException("item " + item + " not found in list");
        } else {
            remove(index);
        }
    }
    
    public void remove(int position) {
        delItem(position);
    }
    
    
    public void delItem(int position) {
        delItems(position, position);
    }
    
    public synchronized int getSelectedIndex() {
        int[] sel = getSelectedIndexes();
        return (sel.length == 1) ? sel[0] : -1;
    }
    
    public synchronized int[] getSelectedIndexes() {
        ListPeer peer = (ListPeer)(ListPeer)this.peer;
        if (peer != null) {
            selected = ((ListPeer)peer).getSelectedIndexes();
        }
        return (int[])(int[])selected.clone();
    }
    
    public synchronized String getSelectedItem() {
        int index = getSelectedIndex();
        return (index < 0) ? null : getItem(index);
    }
    
    public synchronized String[] getSelectedItems() {
        int[] sel = getSelectedIndexes();
        String[] str = new String[sel.length];
        for (int i = 0; i < sel.length; i++) {
            str[i] = getItem(sel[i]);
        }
        return str;
    }
    
    public Object[] getSelectedObjects() {
        return getSelectedItems();
    }
    
    public void select(int index) {
        ListPeer peer;
        do {
            peer = (ListPeer)(ListPeer)this.peer;
            if (peer != null) {
                peer.select(index);
                return;
            }
            synchronized (this) {
                boolean alreadySelected = false;
                for (int i = 0; i < selected.length; i++) {
                    if (selected[i] == index) {
                        alreadySelected = true;
                        break;
                    }
                }
                if (!alreadySelected) {
                    if (!multipleMode) {
                        selected = new int[1];
                        selected[0] = index;
                    } else {
                        int[] newsel = new int[selected.length + 1];
                        System.arraycopy(selected, 0, newsel, 0, selected.length);
                        newsel[selected.length] = index;
                        selected = newsel;
                    }
                }
            }
        }         while (peer != this.peer);
    }
    
    public synchronized void deselect(int index) {
        ListPeer peer = (ListPeer)(ListPeer)this.peer;
        if (peer != null) {
            peer.deselect(index);
        }
        for (int i = 0; i < selected.length; i++) {
            if (selected[i] == index) {
                int[] newsel = new int[selected.length - 1];
                System.arraycopy(selected, 0, newsel, 0, i);
                System.arraycopy(selected, i + 1, newsel, i, selected.length - (i + 1));
                selected = newsel;
                return;
            }
        }
    }
    
    public boolean isIndexSelected(int index) {
        return isSelected(index);
    }
    
    
    public boolean isSelected(int index) {
        int[] sel = getSelectedIndexes();
        for (int i = 0; i < sel.length; i++) {
            if (sel[i] == index) {
                return true;
            }
        }
        return false;
    }
    
    public int getRows() {
        return rows;
    }
    
    public boolean isMultipleMode() {
        return allowsMultipleSelections();
    }
    
    
    public boolean allowsMultipleSelections() {
        return multipleMode;
    }
    
    public void setMultipleMode(boolean b) {
        setMultipleSelections(b);
    }
    
    
    public synchronized void setMultipleSelections(boolean b) {
        if (b != multipleMode) {
            multipleMode = b;
            ListPeer peer = (ListPeer)(ListPeer)this.peer;
            if (peer != null) {
                peer.setMultipleSelections(b);
            }
        }
    }
    
    public int getVisibleIndex() {
        return visibleIndex;
    }
    
    public synchronized void makeVisible(int index) {
        visibleIndex = index;
        ListPeer peer = (ListPeer)(ListPeer)this.peer;
        if (peer != null) {
            peer.makeVisible(index);
        }
    }
    
    public Dimension getPreferredSize(int rows) {
        return preferredSize(rows);
    }
    
    
    public Dimension preferredSize(int rows) {
        synchronized (getTreeLock()) {
            ListPeer peer = (ListPeer)(ListPeer)this.peer;
            return (peer != null) ? peer.preferredSize(rows) : super.preferredSize();
        }
    }
    
    public Dimension getPreferredSize() {
        return preferredSize();
    }
    
    
    public Dimension preferredSize() {
        synchronized (getTreeLock()) {
            return (rows > 0) ? preferredSize(rows) : super.preferredSize();
        }
    }
    
    public Dimension getMinimumSize(int rows) {
        return minimumSize(rows);
    }
    
    
    public Dimension minimumSize(int rows) {
        synchronized (getTreeLock()) {
            ListPeer peer = (ListPeer)(ListPeer)this.peer;
            return (peer != null) ? peer.minimumSize(rows) : super.minimumSize();
        }
    }
    
    public Dimension getMinimumSize() {
        return minimumSize();
    }
    
    
    public Dimension minimumSize() {
        synchronized (getTreeLock()) {
            return (rows > 0) ? minimumSize(rows) : super.minimumSize();
        }
    }
    
    public synchronized void addItemListener(ItemListener l) {
        if (l == null) {
            return;
        }
        itemListener = AWTEventMulticaster.add(itemListener, l);
        newEventsOnly = true;
    }
    
    public synchronized void removeItemListener(ItemListener l) {
        if (l == null) {
            return;
        }
        itemListener = AWTEventMulticaster.remove(itemListener, l);
    }
    
    public synchronized ItemListener[] getItemListeners() {
        return (ItemListener[])((ItemListener[])getListeners(ItemListener.class));
    }
    
    public synchronized void addActionListener(ActionListener l) {
        if (l == null) {
            return;
        }
        actionListener = AWTEventMulticaster.add(actionListener, l);
        newEventsOnly = true;
    }
    
    public synchronized void removeActionListener(ActionListener l) {
        if (l == null) {
            return;
        }
        actionListener = AWTEventMulticaster.remove(actionListener, l);
    }
    
    public synchronized ActionListener[] getActionListeners() {
        return (ActionListener[])((ActionListener[])getListeners(ActionListener.class));
    }
    
    public EventListener[] getListeners(Class listenerType) {
        EventListener l = null;
        if (listenerType == ActionListener.class) {
            l = actionListener;
        } else if (listenerType == ItemListener.class) {
            l = itemListener;
        } else {
            return super.getListeners(listenerType);
        }
        return AWTEventMulticaster.getListeners(l, listenerType);
    }
    
    boolean eventEnabled(AWTEvent e) {
        switch (e.id) {
        case ActionEvent.ACTION_PERFORMED: 
            if ((eventMask & AWTEvent.ACTION_EVENT_MASK) != 0 || actionListener != null) {
                return true;
            }
            return false;
        
        case ItemEvent.ITEM_STATE_CHANGED: 
            if ((eventMask & AWTEvent.ITEM_EVENT_MASK) != 0 || itemListener != null) {
                return true;
            }
            return false;
        
        default: 
            break;
        
        }
        return super.eventEnabled(e);
    }
    
    protected void processEvent(AWTEvent e) {
        if (e instanceof ItemEvent) {
            processItemEvent((ItemEvent)(ItemEvent)e);
            return;
        } else if (e instanceof ActionEvent) {
            processActionEvent((ActionEvent)(ActionEvent)e);
            return;
        }
        super.processEvent(e);
    }
    
    protected void processItemEvent(ItemEvent e) {
        ItemListener listener = itemListener;
        if (listener != null) {
            listener.itemStateChanged(e);
        }
    }
    
    protected void processActionEvent(ActionEvent e) {
        ActionListener listener = actionListener;
        if (listener != null) {
            listener.actionPerformed(e);
        }
    }
    
    protected String paramString() {
        return super.paramString() + ",selected=" + getSelectedItem();
    }
    
    
    public synchronized void delItems(int start, int end) {
        for (int i = end; i >= start; i--) {
            items.removeElementAt(i);
        }
        ListPeer peer = (ListPeer)(ListPeer)this.peer;
        if (peer != null) {
            peer.delItems(start, end);
        }
    }
    private int listSerializedDataVersion = 1;
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        synchronized (this) {
            ListPeer peer = (ListPeer)(ListPeer)this.peer;
            if (peer != null) {
                selected = peer.getSelectedIndexes();
            }
        }
        s.defaultWriteObject();
        AWTEventMulticaster.save(s, itemListenerK, itemListener);
        AWTEventMulticaster.save(s, actionListenerK, actionListener);
        s.writeObject(null);
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException, HeadlessException {
        GraphicsEnvironment.checkHeadless();
        s.defaultReadObject();
        Object keyOrNull;
        while (null != (keyOrNull = s.readObject())) {
            String key = ((String)(String)keyOrNull).intern();
            if (itemListenerK == key) addItemListener((ItemListener)((ItemListener)s.readObject())); else if (actionListenerK == key) addActionListener((ActionListener)((ActionListener)s.readObject())); else s.readObject();
        }
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new List$AccessibleAWTList(this);
        }
        return accessibleContext;
    }
    {
    }
}
