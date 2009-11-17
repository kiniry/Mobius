package java.lang;

import java.util.Comparator;

class String$CaseInsensitiveComparator implements Comparator, java.io.Serializable {
    
    /*synthetic*/ String$CaseInsensitiveComparator(java.lang.String$1 x0) {
        this();
    }
    
    private String$CaseInsensitiveComparator() {
        
    }
    private static final long serialVersionUID = 8575799808933029326L;
    
    public int compare(String s1, String s2) {
        int n1 = s1.length();
        int n2 = s2.length();
        for (int i1 = 0, i2 = 0; i1 < n1 && i2 < n2; i1++, i2++) {
            char c1 = s1.charAt(i1);
            char c2 = s2.charAt(i2);
            if (c1 != c2) {
                c1 = Character.toUpperCase(c1);
                c2 = Character.toUpperCase(c2);
                if (c1 != c2) {
                    c1 = Character.toLowerCase(c1);
                    c2 = Character.toLowerCase(c2);
                    if (c1 != c2) {
                        return c1 - c2;
                    }
                }
            }
        }
        return n1 - n2;
    }
    
    /*synthetic*/ public int compare(Object x0, Object x1) {
        return this.compare((String)x0, (String)x1);
    }
}
