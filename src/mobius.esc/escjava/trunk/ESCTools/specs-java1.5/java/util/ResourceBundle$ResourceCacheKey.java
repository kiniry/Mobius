package java.util;

final class ResourceBundle$ResourceCacheKey implements Cloneable {
    
    /*synthetic*/ ResourceBundle$ResourceCacheKey(java.util.ResourceBundle$1 x0) {
        this();
    }
    
    private ResourceBundle$ResourceCacheKey() {
        
    }
    private ResourceBundle$LoaderReference loaderRef;
    private String searchName;
    private Locale defaultLocale;
    private int hashCodeCache;
    
    public boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        try {
            final ResourceBundle$ResourceCacheKey otherEntry = (ResourceBundle$ResourceCacheKey)(ResourceBundle$ResourceCacheKey)other;
            if (hashCodeCache != otherEntry.hashCodeCache) {
                return false;
            }
            if (!searchName.equals(otherEntry.searchName)) {
                return false;
            }
            if (defaultLocale == null) {
                if (otherEntry.defaultLocale != null) {
                    return false;
                }
            } else {
                if (!defaultLocale.equals(otherEntry.defaultLocale)) {
                    return false;
                }
            }
            if (loaderRef == null) {
                return otherEntry.loaderRef == null;
            } else {
                Object loaderRefValue = loaderRef.get();
                return (otherEntry.loaderRef != null) && (loaderRefValue != null) && (loaderRefValue == otherEntry.loaderRef.get());
            }
        } catch (NullPointerException e) {
            return false;
        } catch (ClassCastException e) {
            return false;
        }
    }
    
    public int hashCode() {
        return hashCodeCache;
    }
    
    public Object clone() {
        try {
            ResourceBundle$ResourceCacheKey clone = (ResourceBundle$ResourceCacheKey)(ResourceBundle$ResourceCacheKey)super.clone();
            if (loaderRef != null) {
                clone.loaderRef = new ResourceBundle$LoaderReference(loaderRef.get(), ResourceBundle.access$100(), clone);
            }
            return clone;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    public void setKeyValues(ClassLoader loader, String searchName, Locale defaultLocale) {
        this.searchName = searchName;
        hashCodeCache = searchName.hashCode();
        this.defaultLocale = defaultLocale;
        if (defaultLocale != null) {
            hashCodeCache ^= defaultLocale.hashCode();
        }
        if (loader == null) {
            this.loaderRef = null;
        } else {
            loaderRef = new ResourceBundle$LoaderReference(loader, ResourceBundle.access$100(), this);
            hashCodeCache ^= loader.hashCode();
        }
    }
    
    public void clear() {
        setKeyValues(null, "", null);
    }
}
