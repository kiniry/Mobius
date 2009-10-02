package java.text;

import sun.text.Normalizer;
import sun.text.NormalizerUtilities;

public class RuleBasedCollator extends Collator {
    
    public RuleBasedCollator(String rules) throws ParseException {
        this(rules, Collator.CANONICAL_DECOMPOSITION);
    }
    
    RuleBasedCollator(String rules, int decomp) throws ParseException {
        
        setStrength(Collator.TERTIARY);
        setDecomposition(decomp);
        tables = new RBCollationTables(rules, decomp);
    }
    
    private RuleBasedCollator(RuleBasedCollator that) {
        
        setStrength(that.getStrength());
        setDecomposition(that.getDecomposition());
        tables = that.tables;
    }
    
    public String getRules() {
        return tables.getRules();
    }
    
    public CollationElementIterator getCollationElementIterator(String source) {
        return new CollationElementIterator(source, this);
    }
    
    public CollationElementIterator getCollationElementIterator(CharacterIterator source) {
        return new CollationElementIterator(source, this);
    }
    
    public synchronized int compare(String source, String target) {
        int result = Collator.EQUAL;
        if (sourceCursor == null) {
            sourceCursor = getCollationElementIterator(source);
        } else {
            sourceCursor.setText(source);
        }
        if (targetCursor == null) {
            targetCursor = getCollationElementIterator(target);
        } else {
            targetCursor.setText(target);
        }
        int sOrder = 0;
        int tOrder = 0;
        boolean initialCheckSecTer = getStrength() >= Collator.SECONDARY;
        boolean checkSecTer = initialCheckSecTer;
        boolean checkTertiary = getStrength() >= Collator.TERTIARY;
        boolean gets = true;
        boolean gett = true;
        while (true) {
            if (gets) sOrder = sourceCursor.next(); else gets = true;
            if (gett) tOrder = targetCursor.next(); else gett = true;
            if ((sOrder == CollationElementIterator.NULLORDER) || (tOrder == CollationElementIterator.NULLORDER)) break;
            int pSOrder = CollationElementIterator.primaryOrder(sOrder);
            int pTOrder = CollationElementIterator.primaryOrder(tOrder);
            if (sOrder == tOrder) {
                if (tables.isFrenchSec() && pSOrder != 0) {
                    if (!checkSecTer) {
                        checkSecTer = initialCheckSecTer;
                        checkTertiary = false;
                    }
                }
                continue;
            }
            if (pSOrder != pTOrder) {
                if (sOrder == 0) {
                    gett = false;
                    continue;
                }
                if (tOrder == 0) {
                    gets = false;
                    continue;
                }
                if (pSOrder == 0) {
                    if (checkSecTer) {
                        result = Collator.GREATER;
                        checkSecTer = false;
                    }
                    gett = false;
                } else if (pTOrder == 0) {
                    if (checkSecTer) {
                        result = Collator.LESS;
                        checkSecTer = false;
                    }
                    gets = false;
                } else {
                    if (pSOrder < pTOrder) {
                        return Collator.LESS;
                    } else {
                        return Collator.GREATER;
                    }
                }
            } else {
                if (checkSecTer) {
                    short secSOrder = CollationElementIterator.secondaryOrder(sOrder);
                    short secTOrder = CollationElementIterator.secondaryOrder(tOrder);
                    if (secSOrder != secTOrder) {
                        result = (secSOrder < secTOrder) ? Collator.LESS : Collator.GREATER;
                        checkSecTer = false;
                    } else {
                        if (checkTertiary) {
                            short terSOrder = CollationElementIterator.tertiaryOrder(sOrder);
                            short terTOrder = CollationElementIterator.tertiaryOrder(tOrder);
                            if (terSOrder != terTOrder) {
                                result = (terSOrder < terTOrder) ? Collator.LESS : Collator.GREATER;
                                checkTertiary = false;
                            }
                        }
                    }
                }
            }
        }
        if (sOrder != CollationElementIterator.NULLORDER) {
            do {
                if (CollationElementIterator.primaryOrder(sOrder) != 0) {
                    return Collator.GREATER;
                } else if (CollationElementIterator.secondaryOrder(sOrder) != 0) {
                    if (checkSecTer) {
                        result = Collator.GREATER;
                        checkSecTer = false;
                    }
                }
            }             while ((sOrder = sourceCursor.next()) != CollationElementIterator.NULLORDER);
        } else if (tOrder != CollationElementIterator.NULLORDER) {
            do {
                if (CollationElementIterator.primaryOrder(tOrder) != 0) return Collator.LESS; else if (CollationElementIterator.secondaryOrder(tOrder) != 0) {
                    if (checkSecTer) {
                        result = Collator.LESS;
                        checkSecTer = false;
                    }
                }
            }             while ((tOrder = targetCursor.next()) != CollationElementIterator.NULLORDER);
        }
        if (result == 0 && getStrength() == IDENTICAL) {
            Normalizer$Mode mode = NormalizerUtilities.toNormalizerMode(getDecomposition());
            String sourceDecomposition = Normalizer.normalize(source, mode, 0);
            String targetDecomposition = Normalizer.normalize(target, mode, 0);
            result = sourceDecomposition.compareTo(targetDecomposition);
        }
        return result;
    }
    
    public synchronized CollationKey getCollationKey(String source) {
        if (source == null) return null;
        if (primResult == null) {
            primResult = new StringBuffer();
            secResult = new StringBuffer();
            terResult = new StringBuffer();
        } else {
            primResult.setLength(0);
            secResult.setLength(0);
            terResult.setLength(0);
        }
        int order = 0;
        boolean compareSec = (getStrength() >= Collator.SECONDARY);
        boolean compareTer = (getStrength() >= Collator.TERTIARY);
        int secOrder = CollationElementIterator.NULLORDER;
        int terOrder = CollationElementIterator.NULLORDER;
        int preSecIgnore = 0;
        if (sourceCursor == null) {
            sourceCursor = getCollationElementIterator(source);
        } else {
            sourceCursor.setText(source);
        }
        while ((order = sourceCursor.next()) != CollationElementIterator.NULLORDER) {
            secOrder = CollationElementIterator.secondaryOrder(order);
            terOrder = CollationElementIterator.tertiaryOrder(order);
            if (!CollationElementIterator.isIgnorable(order)) {
                primResult.append((char)(CollationElementIterator.primaryOrder(order) + COLLATIONKEYOFFSET));
                if (compareSec) {
                    if (tables.isFrenchSec() && preSecIgnore < secResult.length()) {
                        RBCollationTables.reverse(secResult, preSecIgnore, secResult.length());
                    }
                    secResult.append((char)(secOrder + COLLATIONKEYOFFSET));
                    preSecIgnore = secResult.length();
                }
                if (compareTer) {
                    terResult.append((char)(terOrder + COLLATIONKEYOFFSET));
                }
            } else {
                if (compareSec && secOrder != 0) secResult.append((char)(secOrder + tables.getMaxSecOrder() + COLLATIONKEYOFFSET));
                if (compareTer && terOrder != 0) terResult.append((char)(terOrder + tables.getMaxTerOrder() + COLLATIONKEYOFFSET));
            }
        }
        if (tables.isFrenchSec()) {
            if (preSecIgnore < secResult.length()) {
                RBCollationTables.reverse(secResult, preSecIgnore, secResult.length());
            }
            RBCollationTables.reverse(secResult, 0, secResult.length());
        }
        primResult.append((char)0);
        secResult.append((char)0);
        secResult.append(terResult.toString());
        primResult.append(secResult.toString());
        if (getStrength() == IDENTICAL) {
            primResult.append((char)0);
            Normalizer$Mode mode = NormalizerUtilities.toNormalizerMode(getDecomposition());
            primResult.append(Normalizer.normalize(source, mode, 0));
        }
        return new CollationKey(source, primResult.toString());
    }
    
    public Object clone() {
        if (getClass() == RuleBasedCollator.class) {
            return new RuleBasedCollator(this);
        } else {
            RuleBasedCollator result = (RuleBasedCollator)(RuleBasedCollator)super.clone();
            result.primResult = null;
            result.secResult = null;
            result.terResult = null;
            result.sourceCursor = null;
            result.targetCursor = null;
            return result;
        }
    }
    
    public boolean equals(Object obj) {
        if (obj == null) return false;
        if (!super.equals(obj)) return false;
        RuleBasedCollator other = (RuleBasedCollator)(RuleBasedCollator)obj;
        return (getRules().equals(other.getRules()));
    }
    
    public int hashCode() {
        return getRules().hashCode();
    }
    
    RBCollationTables getTables() {
        return tables;
    }
    static final int CHARINDEX = 1879048192;
    static final int EXPANDCHARINDEX = 2113929216;
    static final int CONTRACTCHARINDEX = 2130706432;
    static final int UNMAPPED = -1;
    private static final int COLLATIONKEYOFFSET = 1;
    private RBCollationTables tables = null;
    private StringBuffer primResult = null;
    private StringBuffer secResult = null;
    private StringBuffer terResult = null;
    private CollationElementIterator sourceCursor = null;
    private CollationElementIterator targetCursor = null;
}
