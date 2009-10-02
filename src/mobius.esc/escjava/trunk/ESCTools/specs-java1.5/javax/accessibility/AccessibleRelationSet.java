package javax.accessibility;

import java.util.Vector;

public class AccessibleRelationSet {
    protected Vector relations = null;
    
    public AccessibleRelationSet() {
        
        relations = null;
    }
    
    public AccessibleRelationSet(AccessibleRelation[] relations) {
        
        if (relations.length != 0) {
            this.relations = new Vector(relations.length);
            for (int i = 0; i < relations.length; i++) {
                add(relations[i]);
            }
        }
    }
    
    public boolean add(AccessibleRelation relation) {
        if (relations == null) {
            relations = new Vector();
        }
        AccessibleRelation existingRelation = get(relation.getKey());
        if (existingRelation == null) {
            relations.addElement(relation);
            return true;
        } else {
            Object[] existingTarget = existingRelation.getTarget();
            Object[] newTarget = relation.getTarget();
            int mergedLength = existingTarget.length + newTarget.length;
            Object[] mergedTarget = new Object[mergedLength];
            for (int i = 0; i < existingTarget.length; i++) {
                mergedTarget[i] = existingTarget[i];
            }
            for (int i = existingTarget.length, j = 0; i < mergedLength; i++, j++) {
                mergedTarget[i] = newTarget[j];
            }
            existingRelation.setTarget(mergedTarget);
        }
        return true;
    }
    
    public void addAll(AccessibleRelation[] relations) {
        if (relations.length != 0) {
            if (this.relations == null) {
                this.relations = new Vector(relations.length);
            }
            for (int i = 0; i < relations.length; i++) {
                add(relations[i]);
            }
        }
    }
    
    public boolean remove(AccessibleRelation relation) {
        if (relations == null) {
            return false;
        } else {
            return relations.removeElement(relation);
        }
    }
    
    public void clear() {
        if (relations != null) {
            relations.removeAllElements();
        }
    }
    
    public int size() {
        if (relations == null) {
            return 0;
        } else {
            return relations.size();
        }
    }
    
    public boolean contains(String key) {
        return get(key) != null;
    }
    
    public AccessibleRelation get(String key) {
        if (relations == null) {
            return null;
        } else {
            int len = relations.size();
            for (int i = 0; i < len; i++) {
                AccessibleRelation relation = (AccessibleRelation)(AccessibleRelation)relations.elementAt(i);
                if (relation != null && relation.getKey().equals(key)) {
                    return relation;
                }
            }
            return null;
        }
    }
    
    public AccessibleRelation[] toArray() {
        if (relations == null) {
            return new AccessibleRelation[0];
        } else {
            AccessibleRelation[] relationArray = new AccessibleRelation[relations.size()];
            for (int i = 0; i < relationArray.length; i++) {
                relationArray[i] = (AccessibleRelation)(AccessibleRelation)relations.elementAt(i);
            }
            return relationArray;
        }
    }
    
    public String toString() {
        String ret = "";
        if ((relations != null) && (relations.size() > 0)) {
            ret = ((AccessibleRelation)((AccessibleRelation)relations.elementAt(0))).toDisplayString();
            for (int i = 1; i < relations.size(); i++) {
                ret = ret + "," + ((AccessibleRelation)((AccessibleRelation)relations.elementAt(i))).toDisplayString();
            }
        }
        return ret;
    }
}
