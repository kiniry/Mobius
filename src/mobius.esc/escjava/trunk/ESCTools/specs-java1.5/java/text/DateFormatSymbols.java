package java.text;

import java.util.Locale;
import java.util.ResourceBundle;
import java.io.Serializable;
import java.lang.ref.SoftReference;
import java.util.Vector;
import java.util.Enumeration;
import sun.text.Utility;
import sun.text.resources.LocaleData;
import java.util.Hashtable;

public class DateFormatSymbols implements Serializable, Cloneable {
    
    public DateFormatSymbols() {
        
        initializeData(Locale.getDefault());
    }
    
    public DateFormatSymbols(Locale locale) {
        
        initializeData(locale);
    }
    String[] eras = null;
    String[] months = null;
    String[] shortMonths = null;
    String[] weekdays = null;
    String[] shortWeekdays = null;
    String[] ampms = null;
    String[][] zoneStrings = null;
    static final String patternChars = "GyMdkHmsSEDFwWahKzZ";
    String localPatternChars = null;
    static final long serialVersionUID = -5987973545549424702L;
    
    public String[] getEras() {
        return duplicate(eras);
    }
    
    public void setEras(String[] newEras) {
        eras = duplicate(newEras);
    }
    
    public String[] getMonths() {
        return duplicate(months);
    }
    
    public void setMonths(String[] newMonths) {
        months = duplicate(newMonths);
    }
    
    public String[] getShortMonths() {
        return duplicate(shortMonths);
    }
    
    public void setShortMonths(String[] newShortMonths) {
        shortMonths = duplicate(newShortMonths);
    }
    
    public String[] getWeekdays() {
        return duplicate(weekdays);
    }
    
    public void setWeekdays(String[] newWeekdays) {
        weekdays = duplicate(newWeekdays);
    }
    
    public String[] getShortWeekdays() {
        return duplicate(shortWeekdays);
    }
    
    public void setShortWeekdays(String[] newShortWeekdays) {
        shortWeekdays = duplicate(newShortWeekdays);
    }
    
    public String[] getAmPmStrings() {
        return duplicate(ampms);
    }
    
    public void setAmPmStrings(String[] newAmpms) {
        ampms = duplicate(newAmpms);
    }
    
    public String[][] getZoneStrings() {
        String[][] aCopy = new String[zoneStrings.length][];
        for (int i = 0; i < zoneStrings.length; ++i) aCopy[i] = duplicate(zoneStrings[i]);
        return aCopy;
    }
    
    public void setZoneStrings(String[][] newZoneStrings) {
        String[][] aCopy = new String[newZoneStrings.length][];
        for (int i = 0; i < newZoneStrings.length; ++i) aCopy[i] = duplicate(newZoneStrings[i]);
        zoneStrings = aCopy;
    }
    
    public String getLocalPatternChars() {
        return new String(localPatternChars);
    }
    
    public void setLocalPatternChars(String newLocalPatternChars) {
        localPatternChars = new String(newLocalPatternChars);
    }
    
    public Object clone() {
        try {
            DateFormatSymbols other = (DateFormatSymbols)(DateFormatSymbols)super.clone();
            copyMembers(this, other);
            return other;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    public int hashCode() {
        int hashcode = 0;
        for (int index = 0; index < this.zoneStrings[0].length; ++index) hashcode ^= this.zoneStrings[0][index].hashCode();
        return hashcode;
    }
    
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        DateFormatSymbols that = (DateFormatSymbols)(DateFormatSymbols)obj;
        return (Utility.arrayEquals(eras, that.eras) && Utility.arrayEquals(months, that.months) && Utility.arrayEquals(shortMonths, that.shortMonths) && Utility.arrayEquals(weekdays, that.weekdays) && Utility.arrayEquals(shortWeekdays, that.shortWeekdays) && Utility.arrayEquals(ampms, that.ampms) && Utility.arrayEquals(zoneStrings, that.zoneStrings) && Utility.arrayEquals(localPatternChars, that.localPatternChars));
    }
    static final int millisPerHour = 60 * 60 * 1000;
    private static Hashtable cachedLocaleData = new Hashtable(3);
    private static Hashtable cachedZoneData = new Hashtable();
    
    private ResourceBundle[] cacheLookup(Locale desiredLocale) {
        ResourceBundle[] rbs = new ResourceBundle[2];
        SoftReference[] data = (SoftReference[])(SoftReference[])cachedLocaleData.get(desiredLocale);
        if (data == null) {
            rbs[0] = LocaleData.getLocaleElements(desiredLocale);
            rbs[1] = LocaleData.getDateFormatZoneData(desiredLocale);
            data = new SoftReference[]{new SoftReference(rbs[0]), new SoftReference(rbs[1])};
            cachedLocaleData.put(desiredLocale, data);
        } else {
            ResourceBundle r;
            if ((r = (ResourceBundle)(ResourceBundle)data[0].get()) == null) {
                r = LocaleData.getLocaleElements(desiredLocale);
                data[0] = new SoftReference(r);
            }
            rbs[0] = r;
            if ((r = (ResourceBundle)(ResourceBundle)data[1].get()) == null) {
                r = LocaleData.getDateFormatZoneData(desiredLocale);
                data[1] = new SoftReference(r);
            }
            rbs[1] = r;
        }
        return rbs;
    }
    
    private String[][] loadZoneStrings(Locale desiredLocale, ResourceBundle rsrc) {
        String[][] zones;
        SoftReference data = (SoftReference)(SoftReference)cachedZoneData.get(desiredLocale);
        if (data == null || ((zones = (String[][])(String[][])data.get()) == null)) {
            Vector vec = new Vector();
            Enumeration keys = rsrc.getKeys();
            while (keys.hasMoreElements()) {
                String key = (String)(String)keys.nextElement();
                if (!key.equals("localPatternChars") && !key.equals("zoneStrings")) {
                    vec.add(rsrc.getObject(key));
                }
            }
            zones = new String[vec.size()][];
            vec.toArray(zones);
            data = new SoftReference(zones);
            cachedZoneData.put(desiredLocale, data);
        }
        return zones;
    }
    
    private void initializeData(Locale desiredLocale) {
        int i;
        ResourceBundle[] rbs = cacheLookup(desiredLocale);
        ResourceBundle resource = rbs[0];
        ResourceBundle zoneResource = rbs[1];
        eras = (String[])(String[])resource.getObject("Eras");
        months = resource.getStringArray("MonthNames");
        shortMonths = resource.getStringArray("MonthAbbreviations");
        String[] lWeekdays = resource.getStringArray("DayNames");
        weekdays = new String[8];
        weekdays[0] = "";
        for (i = 0; i < lWeekdays.length; i++) weekdays[i + 1] = lWeekdays[i];
        String[] sWeekdays = resource.getStringArray("DayAbbreviations");
        shortWeekdays = new String[8];
        shortWeekdays[0] = "";
        for (i = 0; i < sWeekdays.length; i++) shortWeekdays[i + 1] = sWeekdays[i];
        ampms = resource.getStringArray("AmPmMarkers");
        zoneStrings = (String[][])loadZoneStrings(desiredLocale, zoneResource);
        localPatternChars = (String)(String)zoneResource.getObject("localPatternChars");
    }
    
    final int getZoneIndex(String ID) {
        for (int index = 0; index < zoneStrings.length; index++) {
            if (ID.equalsIgnoreCase(zoneStrings[index][0])) return index;
        }
        return -1;
    }
    
    private final String[] duplicate(String[] srcArray) {
        String[] dstArray = new String[srcArray.length];
        System.arraycopy(srcArray, 0, dstArray, 0, srcArray.length);
        return dstArray;
    }
    
    private final void copyMembers(DateFormatSymbols src, DateFormatSymbols dst) {
        dst.eras = duplicate(src.eras);
        dst.months = duplicate(src.months);
        dst.shortMonths = duplicate(src.shortMonths);
        dst.weekdays = duplicate(src.weekdays);
        dst.shortWeekdays = duplicate(src.shortWeekdays);
        dst.ampms = duplicate(src.ampms);
        for (int i = 0; i < dst.zoneStrings.length; ++i) dst.zoneStrings[i] = duplicate(src.zoneStrings[i]);
        dst.localPatternChars = new String(src.localPatternChars);
    }
    
    private final boolean equals(String[] current, String[] other) {
        int count = current.length;
        for (int i = 0; i < count; ++i) if (!current[i].equals(other[i])) return false;
        return true;
    }
}
