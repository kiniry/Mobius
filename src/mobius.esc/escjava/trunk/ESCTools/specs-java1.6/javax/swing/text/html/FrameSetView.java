package javax.swing.text.html;

import java.awt.*;
import java.util.*;
import javax.swing.*;
import javax.swing.text.*;
import javax.swing.event.*;

class FrameSetView extends javax.swing.text.BoxView {
    String[] children;
    int[] percentChildren;
    int[] absoluteChildren;
    int[] relativeChildren;
    int percentTotals;
    int absoluteTotals;
    int relativeTotals;
    
    public FrameSetView(Element elem, int axis) {
        super(elem, axis);
        children = null;
    }
    
    private String[] parseRowColSpec(HTML$Attribute key) {
        AttributeSet attributes = getElement().getAttributes();
        String spec = "*";
        if (attributes != null) {
            if (attributes.getAttribute(key) != null) {
                spec = (String)(String)attributes.getAttribute(key);
            }
        }
        StringTokenizer tokenizer = new StringTokenizer(spec, ",");
        int nTokens = tokenizer.countTokens();
        int n = getViewCount();
        String[] items = new String[Math.max(nTokens, n)];
        int i = 0;
        for (; i < nTokens; i++) {
            items[i] = tokenizer.nextToken().trim();
            if (items[i].equals("100%")) {
                items[i] = "*";
            }
        }
        for (; i < items.length; i++) {
            items[i] = "*";
        }
        return items;
    }
    
    private void init() {
        if (getAxis() == View.Y_AXIS) {
            children = parseRowColSpec(HTML$Attribute.ROWS);
        } else {
            children = parseRowColSpec(HTML$Attribute.COLS);
        }
        percentChildren = new int[children.length];
        relativeChildren = new int[children.length];
        absoluteChildren = new int[children.length];
        for (int i = 0; i < children.length; i++) {
            percentChildren[i] = -1;
            relativeChildren[i] = -1;
            absoluteChildren[i] = -1;
            if (children[i].endsWith("*")) {
                if (children[i].length() > 1) {
                    relativeChildren[i] = Integer.parseInt(children[i].substring(0, children[i].length() - 1));
                    relativeTotals += relativeChildren[i];
                } else {
                    relativeChildren[i] = 1;
                    relativeTotals += 1;
                }
            } else if (children[i].indexOf('%') != -1) {
                percentChildren[i] = parseDigits(children[i]);
                percentTotals += percentChildren[i];
            } else {
                absoluteChildren[i] = Integer.parseInt(children[i]);
            }
        }
        if (percentTotals > 100) {
            for (int i = 0; i < percentChildren.length; i++) {
                if (percentChildren[i] > 0) {
                    percentChildren[i] = (percentChildren[i] * 100) / percentTotals;
                }
            }
            percentTotals = 100;
        }
    }
    
    protected void layoutMajorAxis(int targetSpan, int axis, int[] offsets, int[] spans) {
        if (children == null) {
            init();
        }
        SizeRequirements.calculateTiledPositions(targetSpan, null, getChildRequests(targetSpan, axis), offsets, spans);
    }
    
    protected SizeRequirements[] getChildRequests(int targetSpan, int axis) {
        int[] span = new int[children.length];
        spread(targetSpan, span);
        int n = getViewCount();
        SizeRequirements[] reqs = new SizeRequirements[n];
        for (int i = 0, sIndex = 0; i < n; i++) {
            View v = getView(i);
            if ((v instanceof FrameView) || (v instanceof FrameSetView)) {
                reqs[i] = new SizeRequirements((int)v.getMinimumSpan(axis), span[sIndex], (int)v.getMaximumSpan(axis), 0.5F);
                sIndex++;
            } else {
                int min = (int)v.getMinimumSpan(axis);
                int pref = (int)v.getPreferredSpan(axis);
                int max = (int)v.getMaximumSpan(axis);
                float a = v.getAlignment(axis);
                reqs[i] = new SizeRequirements(min, pref, max, a);
            }
        }
        return reqs;
    }
    
    private void spread(int targetSpan, int[] span) {
        if (targetSpan == 0) {
            return;
        }
        int tempSpace = 0;
        int remainingSpace = targetSpan;
        for (int i = 0; i < span.length; i++) {
            if (absoluteChildren[i] > 0) {
                span[i] = absoluteChildren[i];
                remainingSpace -= span[i];
            }
        }
        tempSpace = remainingSpace;
        for (int i = 0; i < span.length; i++) {
            if (percentChildren[i] > 0 && tempSpace > 0) {
                span[i] = (percentChildren[i] * tempSpace) / 100;
                remainingSpace -= span[i];
            } else if (percentChildren[i] > 0 && tempSpace <= 0) {
                span[i] = targetSpan / span.length;
                remainingSpace -= span[i];
            }
        }
        if (remainingSpace > 0 && relativeTotals > 0) {
            for (int i = 0; i < span.length; i++) {
                if (relativeChildren[i] > 0) {
                    span[i] = (remainingSpace * relativeChildren[i]) / relativeTotals;
                }
            }
        } else if (remainingSpace > 0) {
            float vTotal = (float)(targetSpan - remainingSpace);
            float[] tempPercents = new float[span.length];
            remainingSpace = targetSpan;
            for (int i = 0; i < span.length; i++) {
                tempPercents[i] = ((float)span[i] / vTotal) * 100.0F;
                span[i] = (int)(((float)targetSpan * tempPercents[i]) / 100.0F);
                remainingSpace -= span[i];
            }
            int i = 0;
            while (remainingSpace != 0) {
                if (remainingSpace < 0) {
                    span[i++]--;
                    remainingSpace++;
                } else {
                    span[i++]++;
                    remainingSpace--;
                }
                if (i == span.length) i = 0;
            }
        }
    }
    
    private int parseDigits(String mixedStr) {
        int result = 0;
        for (int i = 0; i < mixedStr.length(); i++) {
            char ch = mixedStr.charAt(i);
            if (Character.isDigit(ch)) {
                result = (result * 10) + Character.digit(ch, 10);
            }
        }
        return result;
    }
}
