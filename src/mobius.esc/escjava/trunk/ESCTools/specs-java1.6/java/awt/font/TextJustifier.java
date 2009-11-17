package java.awt.font;

class TextJustifier {
    private GlyphJustificationInfo[] info;
    private int start;
    private int limit;
    static boolean DEBUG = false;
    
    TextJustifier(GlyphJustificationInfo[] info, int start, int limit) {
        
        this.info = info;
        this.start = start;
        this.limit = limit;
        if (DEBUG) {
            System.out.println("start: " + start + ", limit: " + limit);
            for (int i = start; i < limit; i++) {
                GlyphJustificationInfo gji = info[i];
                System.out.println("w: " + gji.weight + ", gp: " + gji.growPriority + ", gll: " + gji.growLeftLimit + ", grl: " + gji.growRightLimit);
            }
        }
    }
    public static final int MAX_PRIORITY = 3;
    
    public float[] justify(float delta) {
        float[] deltas = new float[info.length * 2];
        boolean grow = delta > 0;
        if (DEBUG) System.out.println("delta: " + delta);
        int fallbackPriority = -1;
        for (int p = 0; delta != 0; p++) {
            boolean lastPass = p > MAX_PRIORITY;
            if (lastPass) p = fallbackPriority;
            float weight = 0;
            float gslimit = 0;
            float absorbweight = 0;
            for (int i = start; i < limit; i++) {
                GlyphJustificationInfo gi = info[i];
                if ((grow ? gi.growPriority : gi.shrinkPriority) == p) {
                    if (fallbackPriority == -1) {
                        fallbackPriority = p;
                    }
                    if (i != start) {
                        weight += gi.weight;
                        if (grow) {
                            gslimit += gi.growLeftLimit;
                            if (gi.growAbsorb) {
                                absorbweight += gi.weight;
                            }
                        } else {
                            gslimit += gi.shrinkLeftLimit;
                            if (gi.shrinkAbsorb) {
                                absorbweight += gi.weight;
                            }
                        }
                    }
                    if (i + 1 != limit) {
                        weight += gi.weight;
                        if (grow) {
                            gslimit += gi.growRightLimit;
                            if (gi.growAbsorb) {
                                absorbweight += gi.weight;
                            }
                        } else {
                            gslimit += gi.shrinkRightLimit;
                            if (gi.shrinkAbsorb) {
                                absorbweight += gi.weight;
                            }
                        }
                    }
                }
            }
            if (!grow) {
                gslimit = -gslimit;
            }
            boolean hitLimit = (weight == 0) || (!lastPass && ((delta < 0) == (delta < gslimit)));
            boolean absorbing = hitLimit && absorbweight > 0;
            float weightedDelta = delta / weight;
            float weightedAbsorb = 0;
            if (hitLimit && absorbweight > 0) {
                weightedAbsorb = (delta - gslimit) / absorbweight;
            }
            if (DEBUG) {
                System.out.println("pass: " + p + ", d: " + delta + ", l: " + gslimit + ", w: " + weight + ", aw: " + absorbweight + ", wd: " + weightedDelta + ", wa: " + weightedAbsorb + ", hit: " + (hitLimit ? "y" : "n"));
            }
            int n = start * 2;
            for (int i = start; i < limit; i++) {
                GlyphJustificationInfo gi = info[i];
                if ((grow ? gi.growPriority : gi.shrinkPriority) == p) {
                    if (i != start) {
                        float d;
                        if (hitLimit) {
                            d = grow ? gi.growLeftLimit : -gi.shrinkLeftLimit;
                            if (absorbing) {
                                d += gi.weight * weightedAbsorb;
                            }
                        } else {
                            d = gi.weight * weightedDelta;
                        }
                        deltas[n] += d;
                    }
                    n++;
                    if (i + 1 != limit) {
                        float d;
                        if (hitLimit) {
                            d = grow ? gi.growRightLimit : -gi.shrinkRightLimit;
                            if (absorbing) {
                                d += gi.weight * weightedAbsorb;
                            }
                        } else {
                            d = gi.weight * weightedDelta;
                        }
                        deltas[n] += d;
                    }
                    n++;
                } else {
                    n += 2;
                }
            }
            if (!lastPass && hitLimit && !absorbing) {
                delta -= gslimit;
            } else {
                delta = 0;
            }
        }
        if (DEBUG) {
            float total = 0;
            for (int i = 0; i < deltas.length; i++) {
                total += deltas[i];
                System.out.print(deltas[i] + ", ");
                if (i % 20 == 9) {
                    System.out.println();
                }
            }
            System.out.println("\ntotal: " + total);
            System.out.println();
        }
        return deltas;
    }
}
