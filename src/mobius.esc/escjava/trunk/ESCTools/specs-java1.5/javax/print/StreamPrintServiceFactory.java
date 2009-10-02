package javax.print;

import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Iterator;
import javax.print.DocFlavor;
import sun.awt.AppContext;

public abstract class StreamPrintServiceFactory {
    
    /*synthetic*/ static ArrayList access$100() {
        return getListOfFactories();
    }
    
    public StreamPrintServiceFactory() {
        
    }
    {
    }
    
    private static StreamPrintServiceFactory$Services getServices() {
        StreamPrintServiceFactory$Services services = (StreamPrintServiceFactory$Services)(StreamPrintServiceFactory$Services)AppContext.getAppContext().get(StreamPrintServiceFactory.Services.class);
        if (services == null) {
            services = new StreamPrintServiceFactory$Services();
            AppContext.getAppContext().put(StreamPrintServiceFactory.Services.class, services);
        }
        return services;
    }
    
    private static ArrayList getListOfFactories() {
        return StreamPrintServiceFactory.Services.access$000(getServices());
    }
    
    private static ArrayList initListOfFactories() {
        ArrayList listOfFactories = new ArrayList();
        StreamPrintServiceFactory.Services.access$002(getServices(), listOfFactories);
        return listOfFactories;
    }
    
    public static StreamPrintServiceFactory[] lookupStreamPrintServiceFactories(DocFlavor flavor, String outputMimeType) {
        ArrayList list = getFactories(flavor, outputMimeType);
        return (StreamPrintServiceFactory[])((StreamPrintServiceFactory[])list.toArray(new StreamPrintServiceFactory[list.size()]));
    }
    
    public abstract String getOutputFormat();
    
    public abstract DocFlavor[] getSupportedDocFlavors();
    
    public abstract StreamPrintService getPrintService(OutputStream out);
    
    private static ArrayList getAllFactories() {
        synchronized (StreamPrintServiceFactory.class) {
            ArrayList listOfFactories = getListOfFactories();
            if (listOfFactories != null) {
                return listOfFactories;
            } else {
                listOfFactories = initListOfFactories();
            }
            try {
                java.security.AccessController.doPrivileged(new StreamPrintServiceFactory$1());
            } catch (java.security.PrivilegedActionException e) {
            }
            return listOfFactories;
        }
    }
    
    private static boolean isMember(DocFlavor flavor, DocFlavor[] flavors) {
        for (int f = 0; f < flavors.length; f++) {
            if (flavor.equals(flavors[f])) {
                return true;
            }
        }
        return false;
    }
    
    private static ArrayList getFactories(DocFlavor flavor, String outType) {
        if (flavor == null && outType == null) {
            return getAllFactories();
        }
        ArrayList list = new ArrayList();
        Iterator iterator = getAllFactories().iterator();
        while (iterator.hasNext()) {
            StreamPrintServiceFactory factory = (StreamPrintServiceFactory)(StreamPrintServiceFactory)iterator.next();
            if ((outType == null || outType.equalsIgnoreCase(factory.getOutputFormat())) && (flavor == null || isMember(flavor, factory.getSupportedDocFlavors()))) {
                list.add(factory);
            }
        }
        return list;
    }
}
