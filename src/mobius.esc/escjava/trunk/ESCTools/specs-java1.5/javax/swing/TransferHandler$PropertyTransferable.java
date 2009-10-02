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

class TransferHandler$PropertyTransferable implements Transferable {
    
    TransferHandler$PropertyTransferable(PropertyDescriptor p, JComponent c) {
        
        property = p;
        component = c;
    }
    
    public DataFlavor[] getTransferDataFlavors() {
        DataFlavor[] flavors = new DataFlavor[1];
        Class propertyType = property.getPropertyType();
        String mimeType = DataFlavor.javaJVMLocalObjectMimeType + ";class=" + propertyType.getName();
        try {
            flavors[0] = new DataFlavor(mimeType);
        } catch (ClassNotFoundException cnfe) {
            flavors = new DataFlavor[0];
        }
        return flavors;
    }
    
    public boolean isDataFlavorSupported(DataFlavor flavor) {
        Class propertyType = property.getPropertyType();
        if ("application".equals(flavor.getPrimaryType()) && "x-java-jvm-local-objectref".equals(flavor.getSubType()) && flavor.getRepresentationClass().isAssignableFrom(propertyType)) {
            return true;
        }
        return false;
    }
    
    public Object getTransferData(DataFlavor flavor) throws UnsupportedFlavorException, IOException {
        if (!isDataFlavorSupported(flavor)) {
            throw new UnsupportedFlavorException(flavor);
        }
        Method reader = property.getReadMethod();
        Object value = null;
        try {
            value = MethodUtil.invoke(reader, component, null);
        } catch (Exception ex) {
            throw new IOException("Property read failed: " + property.getName());
        }
        return value;
    }
    JComponent component;
    PropertyDescriptor property;
}
