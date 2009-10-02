package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.dnd.*;
import java.beans.*;
import java.lang.reflect.*;
import java.io.*;
import javax.swing.event.*;
import sun.reflect.misc.MethodUtil;

public class TransferHandler implements Serializable {
    
    /*synthetic*/ static DropTargetListener access$200() {
        return getDropTargetListener();
    }
    {
    }
    public static final int NONE = DnDConstants.ACTION_NONE;
    public static final int COPY = DnDConstants.ACTION_COPY;
    public static final int MOVE = DnDConstants.ACTION_MOVE;
    public static final int COPY_OR_MOVE = DnDConstants.ACTION_COPY_OR_MOVE;
    private static final int LINK = DnDConstants.ACTION_LINK;
    
    public static Action getCutAction() {
        return cutAction;
    }
    
    public static Action getCopyAction() {
        return copyAction;
    }
    
    public static Action getPasteAction() {
        return pasteAction;
    }
    
    public TransferHandler(String property) {
        
        propertyName = property;
    }
    
    protected TransferHandler() {
        this(null);
    }
    
    public void exportAsDrag(JComponent comp, InputEvent e, int action) {
        int srcActions = getSourceActions(comp);
        int dragAction = srcActions & action;
        if (!(e instanceof MouseEvent)) {
            dragAction = NONE;
        }
        if (dragAction != NONE && !GraphicsEnvironment.isHeadless()) {
            if (recognizer == null) {
                recognizer = new TransferHandler$SwingDragGestureRecognizer(new TransferHandler$DragHandler(null));
            }
            recognizer.gestured(comp, (MouseEvent)(MouseEvent)e, srcActions, dragAction);
        } else {
            exportDone(comp, null, NONE);
        }
    }
    
    public void exportToClipboard(JComponent comp, Clipboard clip, int action) throws IllegalStateException {
        int clipboardAction = getSourceActions(comp) & action;
        if (clipboardAction != NONE) {
            Transferable t = createTransferable(comp);
            if (t != null) {
                try {
                    clip.setContents(t, null);
                    exportDone(comp, t, clipboardAction);
                    return;
                } catch (IllegalStateException ise) {
                    exportDone(comp, t, NONE);
                    throw ise;
                }
            }
        }
        exportDone(comp, null, NONE);
    }
    
    public boolean importData(JComponent comp, Transferable t) {
        PropertyDescriptor prop = getPropertyDescriptor(comp);
        if (prop != null) {
            Method writer = prop.getWriteMethod();
            if (writer == null) {
                return false;
            }
            Class[] params = writer.getParameterTypes();
            if (params.length != 1) {
                return false;
            }
            DataFlavor flavor = getPropertyDataFlavor(params[0], t.getTransferDataFlavors());
            if (flavor != null) {
                try {
                    Object value = t.getTransferData(flavor);
                    Object[] args = {value};
                    MethodUtil.invoke(writer, comp, args);
                    return true;
                } catch (Exception ex) {
                    System.err.println("Invocation failed");
                }
            }
        }
        return false;
    }
    
    public boolean canImport(JComponent comp, DataFlavor[] transferFlavors) {
        PropertyDescriptor prop = getPropertyDescriptor(comp);
        if (prop != null) {
            Method writer = prop.getWriteMethod();
            if (writer == null) {
                return false;
            }
            Class[] params = writer.getParameterTypes();
            if (params.length != 1) {
                return false;
            }
            DataFlavor flavor = getPropertyDataFlavor(params[0], transferFlavors);
            if (flavor != null) {
                return true;
            }
        }
        return false;
    }
    
    public int getSourceActions(JComponent c) {
        PropertyDescriptor prop = getPropertyDescriptor(c);
        if (prop != null) {
            return COPY;
        }
        return NONE;
    }
    
    public Icon getVisualRepresentation(Transferable t) {
        return null;
    }
    
    protected Transferable createTransferable(JComponent c) {
        PropertyDescriptor property = getPropertyDescriptor(c);
        if (property != null) {
            return new TransferHandler$PropertyTransferable(property, c);
        }
        return null;
    }
    
    protected void exportDone(JComponent source, Transferable data, int action) {
    }
    
    private PropertyDescriptor getPropertyDescriptor(JComponent comp) {
        if (propertyName == null) {
            return null;
        }
        Class k = comp.getClass();
        BeanInfo bi;
        try {
            bi = Introspector.getBeanInfo(k);
        } catch (IntrospectionException ex) {
            return null;
        }
        PropertyDescriptor[] props = bi.getPropertyDescriptors();
        for (int i = 0; i < props.length; i++) {
            if (propertyName.equals(props[i].getName())) {
                Method reader = props[i].getReadMethod();
                if (reader != null) {
                    Class[] params = reader.getParameterTypes();
                    if (params == null || params.length == 0) {
                        return props[i];
                    }
                }
            }
        }
        return null;
    }
    
    private DataFlavor getPropertyDataFlavor(Class k, DataFlavor[] flavors) {
        for (int i = 0; i < flavors.length; i++) {
            DataFlavor flavor = flavors[i];
            if ("application".equals(flavor.getPrimaryType()) && "x-java-jvm-local-objectref".equals(flavor.getSubType()) && k.isAssignableFrom(flavor.getRepresentationClass())) {
                return flavor;
            }
        }
        return null;
    }
    private String propertyName;
    private static TransferHandler$SwingDragGestureRecognizer recognizer = null;
    private static DropTargetListener dropLinkage = null;
    
    private static DropTargetListener getDropTargetListener() {
        if (dropLinkage == null) {
            dropLinkage = new TransferHandler$DropHandler(null);
        }
        return dropLinkage;
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    static final Action cutAction = new TransferHandler$TransferAction("cut");
    static final Action copyAction = new TransferHandler$TransferAction("copy");
    static final Action pasteAction = new TransferHandler$TransferAction("paste");
    {
    }
}
