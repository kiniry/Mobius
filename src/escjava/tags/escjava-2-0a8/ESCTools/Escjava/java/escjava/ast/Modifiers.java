// This file was created as aprt of the 2003 Revision of the ESC tools.
// Author: David R. Cok

package escjava.ast;

/** This class adds some JML-specific modifiers to the usual Java set.
*/
public class Modifiers extends javafe.ast.Modifiers {

  public static final int ACC_HELPER = 0x20000; // helper method, model or not
  public static final int ACC_MODEL = 0x80000; // model fields and methods
  public static final int ACC_DESUGARED = 0x400000; // set if desugaring 
					// of routine specs is complete

  public static boolean isModel(int modifiers) {
	return (modifiers&ACC_MODEL) != 0;
  }
  public static boolean isHelper(int modifiers) {
	return (modifiers&ACC_HELPER) != 0;
  }

  //@ ensures \result != null;
  public static String toString(int modifiers) {
    String s = javafe.ast.Modifiers.toString(modifiers);
    if (isModel(modifiers)) s = "model " + s;
    // FIXME if (Utils.isPure(modifiers)) s = "pure " + s;
    if (isHelper(modifiers)) s = "helper " + s;
    return s;
  }

}
