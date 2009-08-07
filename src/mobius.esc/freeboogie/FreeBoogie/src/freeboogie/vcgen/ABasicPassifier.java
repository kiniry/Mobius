package freeboogie.vcgen;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import freeboogie.ast.AssertAssumeCmd;
import freeboogie.ast.AtomId;
import freeboogie.ast.BinaryOp;
import freeboogie.ast.Declaration;
import freeboogie.ast.Expr;
import freeboogie.ast.Transformer;
import freeboogie.ast.VariableDecl;
import freeboogie.tc.TcInterface;
import freeboogie.tc.TypeUtils;

/**
 * Base class for {@code Passivator} and {@code Passifier}.
 */
public abstract class ABasicPassifier extends Transformer {

  private TcInterface fTypeChecker;

  /**
   * Returns the variable declaration corresponding to the given id.
   * @param id the id to check for
   * @return a valid variable declaration or null
   */
  VariableDecl getDeclaration(AtomId id) {
    Declaration decl = getTypeChecker().getST().ids.def(id);
    if (decl instanceof VariableDecl) {
      return (VariableDecl) decl;
    }
    return null;
  }
  public TcInterface getTypeChecker() {
    return fTypeChecker;
  }  

  public void setTypeChecker(TcInterface tc) {
    fTypeChecker = tc;
  }
  
  public static AssertAssumeCmd mkAssumeEQ(Expr left, Expr right) {
    return AssertAssumeCmd.mk(AssertAssumeCmd.CmdType.ASSUME, null,
      BinaryOp.mk(BinaryOp.Op.EQ, left, right));
  }
  
  public static AtomId mkVar(VariableDecl decl, int idx) {
    String name = decl.getName();
    if (idx != 0) {
      name += "$$" + idx;
    }
    return AtomId.mk(name, null);
  }
  
  public static AtomId mkVar(AtomId id, int idx) {
    String name = id.getId();
    if (idx != 0) {
      name += "$$" + idx;
    }
    return  AtomId.mk(name, id.getTypes(), id.loc());
  }
  
  public static VariableDecl mkDecl(VariableDecl old, int idx, Declaration next) {
    String name = old.getName();
    if (idx != 0) {
      name += "$$" + idx;
    }
    return VariableDecl.mk(
      null,
      name,
      TypeUtils.stripDep(old.getType()).clone(),
      old.getTypeArgs() == null? null : old.getTypeArgs().clone(),
      next);
  }

  /**
   * 
   * TODO: description.
   *
   * @author J. Charles (julien.charles@inria.fr)
   * @author reviewed by TODO
   */
  public static class Environment {
    /** global variable list. */
    private final Map<VariableDecl, Integer> global = 
      new LinkedHashMap<VariableDecl, Integer>() ;
    /** local variable list. */
    private final Map<VariableDecl, Integer> local = 
      new LinkedHashMap<VariableDecl, Integer>();
    /** for efficiency. */
    private final Map<VariableDecl, Integer> all = 
      new LinkedHashMap<VariableDecl, Integer>();
    private String currentLocation;
   
    /**
     * Build an environment.
     * @param fileName  */
    public Environment(String fileName) {
     this.currentLocation = fileName;
    }
    
    /**
     * Adds a variable to the global variables set.
     * @param decl the variable to add
     */
    public void addGlobal(VariableDecl decl) {
      global.put(decl, 0);
      all.put(decl, 0);
    }
    
    /**
     * Put a variable in the environment with its corresponding index.
     * @param decl de variable declaration
     * @param i the index
     */
    public void put(VariableDecl decl, int i) {
      if (global.containsKey(decl)) {
        global.put(decl, i);
      } else {
        local.put(decl, i);
      }
      all.put(decl, i);
    }

    /**
     * Returns the global set of variables.
     * @return a set of variables and their indexes
     */
    public Set<Entry<VariableDecl, Integer>> getGlobalSet() {
      return global.entrySet();
    }
    
    /**
     * Returns the local set of variables.
     * @return a set of variables and their indexes
     */
    public Set<Entry<VariableDecl, Integer>> getLocalSet() {
      return local.entrySet();
    }
    
    /**
     * Returns all the collected variables so far.
     * @return a set of variables and their indexes
     */
    public Set<Entry<VariableDecl, Integer>> getAllSet() {
      return all.entrySet();
    }
    
    /**
     * Removes a variable from the environment.
     * @param old the variable to remove
     */
    public void remove(VariableDecl old) {
      global.remove(old);
      local.remove(old);
      all.remove(old);
    }

    /**
     * Put all the variables contained in the given environment
     * in the current environment.
     * @param env
     */
    public void putAll(Environment env) {
      global.putAll(env.global);
      local.putAll(env.local);
      all.putAll(env.all);
    }

    private Environment(Environment env) {
      putAll(env);
    }

    /**
     * Returns the index corresponding to the given variable.
     * @param key the variable to get the index from
     * @return an index > to 0
     */
    public int get(VariableDecl key) {
      Integer i = all.get(key);
      return i == null? 0 : i;
    }
    
    
    @Override
    public Environment clone() {
      return new Environment(this);
    }
    
    /**
     * Update with another environment.
     * ie. if variable index is greater in the other 
     * environment, it replaces the current variable index.
     * @param env the environment to update with.
     */
    public void updateWith(Environment env) {
      update(env.global, global);
      update(env.local, local);
      update(env.all, all);
    }
    
    /**
     * Updates only the global environment with the given values.
     * @param env the environment to update with
     */
    public void updateGlobalWith(Environment env) {
      update(env.global, global);
      all.putAll(global);
    }
    
    private static void update(Map<VariableDecl, Integer> src, 
                               Map<VariableDecl, Integer> target) {

      for (VariableDecl decl: src.keySet()) {
        Integer currInc = target.get(decl);
        int curr = currInc != null? currInc : 0;
        Integer incarnation = src.get(decl);
        if (incarnation > curr) {
              curr = incarnation;
              target.put(decl, curr);
        }
      }
    }
    
    /**
     * toString method to print the global environment.
     * @return the global list of variables
     */
    public String globalToString() {
      return mapToString(global);
    }
  
    /**
     * toString method to print the local environment.
     * @return the local list of variables
     */
    public String localToString() {
      return mapToString(local);
    }

    public static String mapToString(Map<VariableDecl, Integer> map) {
      StringBuilder sb = new StringBuilder();
      for (Entry<VariableDecl, Integer> e : map.entrySet()) {
        VariableDecl vd = e.getKey();
        Integer versions = e.getValue();
        if (versions == 0) continue;
        sb.append(vd.loc());
        sb.append(" ");
        sb.append(vd.getName());
        sb.append(" ");
        sb.append(versions);
        sb.append("\n");
      }
      return sb.toString();
    }

    public String getLoc() {
      return this.currentLocation;
    }


    public String toString() {
      StringBuilder blder = new StringBuilder(); 
      for (Entry<VariableDecl, Integer> ent: all.entrySet()) {
        if (ent.getValue() != 0)
          blder.append(", " + ent.getKey().getName() + " " + ent.getValue());
      }
      if (blder.length() == 0) 
        return "";
      return blder.substring(2);
    }
  }
}
