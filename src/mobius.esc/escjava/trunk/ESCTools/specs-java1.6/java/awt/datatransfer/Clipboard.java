package java.awt.datatransfer;

import java.awt.EventQueue;
import java.util.Set;
import java.util.HashSet;
import java.util.Arrays;
import java.io.IOException;
import sun.awt.EventListenerAggregate;

public class Clipboard {
    String name;
    protected ClipboardOwner owner;
    protected Transferable contents;
    private EventListenerAggregate flavorListeners;
    private Set currentDataFlavors;
    
    public Clipboard(String name) {
        
        this.name = name;
    }
    
    public String getName() {
        return name;
    }
    
    public synchronized void setContents(Transferable contents, ClipboardOwner owner) {
        final ClipboardOwner oldOwner = this.owner;
        final Transferable oldContents = this.contents;
        this.owner = owner;
        this.contents = contents;
        if (oldOwner != null && oldOwner != owner) {
            EventQueue.invokeLater(new Clipboard$1(this, oldOwner, oldContents));
        }
        fireFlavorsChanged();
    }
    
    public synchronized Transferable getContents(Object requestor) {
        return contents;
    }
    
    public DataFlavor[] getAvailableDataFlavors() {
        Transferable cntnts = getContents(null);
        if (cntnts == null) {
            return new DataFlavor[0];
        }
        return cntnts.getTransferDataFlavors();
    }
    
    public boolean isDataFlavorAvailable(DataFlavor flavor) {
        if (flavor == null) {
            throw new NullPointerException("flavor");
        }
        Transferable cntnts = getContents(null);
        if (cntnts == null) {
            return false;
        }
        return cntnts.isDataFlavorSupported(flavor);
    }
    
    public Object getData(DataFlavor flavor) throws UnsupportedFlavorException, IOException {
        if (flavor == null) {
            throw new NullPointerException("flavor");
        }
        Transferable cntnts = getContents(null);
        if (cntnts == null) {
            throw new UnsupportedFlavorException(flavor);
        }
        return cntnts.getTransferData(flavor);
    }
    
    public synchronized void addFlavorListener(FlavorListener listener) {
        if (listener == null) {
            return;
        }
        if (flavorListeners == null) {
            currentDataFlavors = getAvailableDataFlavorSet();
            flavorListeners = new EventListenerAggregate(FlavorListener.class);
        }
        flavorListeners.add(listener);
    }
    
    public synchronized void removeFlavorListener(FlavorListener listener) {
        if (listener == null || flavorListeners == null) {
            return;
        }
        flavorListeners.remove(listener);
    }
    
    public synchronized FlavorListener[] getFlavorListeners() {
        return flavorListeners == null ? new FlavorListener[0] : (FlavorListener[])(FlavorListener[])flavorListeners.getListenersCopy();
    }
    
    private void fireFlavorsChanged() {
        if (flavorListeners == null) {
            return;
        }
        Set prevDataFlavors = currentDataFlavors;
        currentDataFlavors = getAvailableDataFlavorSet();
        if (prevDataFlavors.equals(currentDataFlavors)) {
            return;
        }
        FlavorListener[] flavorListenerArray = (FlavorListener[])(FlavorListener[])flavorListeners.getListenersInternal();
        for (int i = 0; i < flavorListenerArray.length; i++) {
            final FlavorListener listener = flavorListenerArray[i];
            EventQueue.invokeLater(new Clipboard$2(this, listener));
        }
    }
    
    private Set getAvailableDataFlavorSet() {
        Set set = new HashSet();
        Transferable contents = getContents(null);
        if (contents != null) {
            DataFlavor[] flavors = contents.getTransferDataFlavors();
            if (flavors != null) {
                set.addAll(Arrays.asList(flavors));
            }
        }
        return set;
    }
}
