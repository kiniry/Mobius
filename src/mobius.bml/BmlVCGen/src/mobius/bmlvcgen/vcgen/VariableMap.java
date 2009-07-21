package mobius.bmlvcgen.vcgen;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import mobius.bmlvcgen.bml.LocalVariable;

// TODO: Make this structure more efficient.

/**
 * Objects of this class are used to find
 * local variables at given program point.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public final class VariableMap {
  private final List<LocalVariable> locals;
  private boolean dirty;
  
  /**
   * Constructor. Creates empty mapping.
   * @param maxLocals Max possible variable index.
   */
  public VariableMap(final int maxLocals) {
    locals = new ArrayList<LocalVariable>();
    dirty = false;
  }
  
  /**
   * Add a variable to this mapping.
   * @param var Variable.
   */
  public void add(final LocalVariable var) {
    locals.add(var);
    dirty = true;
  }
  
  /**
   * Get local variables at given program point.
   * Variables returned are ordered by 
   * start of scope.
   * @param pc Program counter.
   * @return List of variables.
   */
  public List<LocalVariable> getLocals(final int pc) {
    final List<LocalVariable> result = 
      new ArrayList<LocalVariable>();
    if (dirty) {
      Collections.sort(locals, new LocalComparator());
      dirty = false;
    }
    for (final LocalVariable lv : locals) {
      if (lv.getStart() <= pc && lv.getEnd() >= pc) {
        result.add(lv);
      }
    }
    return result;
  }

  /**
   * Get local variables declared before given program point.
   * Variables returned are ordered by index.
   * @param pc Program counter.
   * @return List of variables.
   */
  public List<LocalVariable> getDeclaredLocals(final int pc) {
    final List<LocalVariable> result = 
      new ArrayList<LocalVariable>();
    for (final LocalVariable lv : locals) {
      if (lv.getStart() <= pc) {
        result.add(lv);
      }
    }
    Collections.sort(result, new IndexComparator());
    return result;
  }
  
  // Compare local variables by scope start.
  private static class LocalComparator 
    implements Comparator<LocalVariable> {

    /** {@inheritDoc} */
    public int compare(final LocalVariable v1, 
                       final LocalVariable v2) {
      final int v1start = v1.getStart();
      final int v2start = v2.getStart();
      if (v1start < v2start) {
        return -1;
      } else if (v1start > v2start) {
        return 1;
      } else {
        return 0;
      }
    }
  }
  
  // Compare local variables by index.
  private static class IndexComparator 
    implements Comparator<LocalVariable> {

    /** {@inheritDoc} */
    public int compare(final LocalVariable v1, 
                       final LocalVariable v2) {
      final int v1index = v1.getIndex();
      final int v2index = v2.getIndex();
      if (v1index < v2index) {
        return -1;
      } else if (v1index > v2index) {
        return 1;
      } else {
        return 0;
      }
    }
  }
}
