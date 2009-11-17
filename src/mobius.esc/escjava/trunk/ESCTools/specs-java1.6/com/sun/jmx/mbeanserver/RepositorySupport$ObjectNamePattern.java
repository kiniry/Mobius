package com.sun.jmx.mbeanserver;

import java.util.Hashtable;
import java.util.Enumeration;
import javax.management.*;

final class RepositorySupport$ObjectNamePattern {
    private final char[] domain;
    private final String[] keys;
    private final String[] values;
    private final String properties;
    private final boolean isPropertyPattern;
    public final ObjectName pattern;
    
    public RepositorySupport$ObjectNamePattern(ObjectName pattern) {
        this(pattern.isPattern(), pattern.getDomain(), pattern.isPropertyPattern(), pattern.getCanonicalKeyPropertyListString(), pattern.getKeyPropertyList(), pattern);
    }
    
    RepositorySupport$ObjectNamePattern(boolean domainPattern, String domain, boolean propertyPattern, String canonicalProps, Hashtable keyPropertyList, ObjectName pattern) {
        
        final int len = (keyPropertyList == null ? 0 : keyPropertyList.size());
        final Enumeration e = (keyPropertyList == null ? null : keyPropertyList.keys());
        this.domain = (domain == null ? null : domain.toCharArray());
        this.keys = new String[len];
        this.values = new String[len];
        for (int i = 0; i < len; i++) {
            final String k = (String)(String)e.nextElement();
            keys[i] = k;
            values[i] = (String)(String)keyPropertyList.get(k);
        }
        this.properties = canonicalProps;
        this.isPropertyPattern = propertyPattern;
        this.pattern = pattern;
    }
    
    public boolean matchKeys(ObjectName name) {
        if (isPropertyPattern) {
            for (int i = keys.length - 1; i >= 0; i--) {
                String v = name.getKeyProperty(keys[i]);
                if (v == null) return false;
                if (v.equals(values[i])) continue;
                return false;
            }
            return true;
        } else {
            if (keys.length != name.getKeyPropertyList().size()) return false;
            final String p1 = name.getCanonicalKeyPropertyListString();
            final String p2 = properties;
            return (p1.equals(p2));
        }
    }
}
