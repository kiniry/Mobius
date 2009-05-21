package astgen;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents a class from the abstract grammar.
 * 
 * @author rgrig 
 * @author Mikolas Janota
 */
public class AgClass implements Comparable<AgClass> {
  /** The name of the class. */
  public String name = null;
  
  /** The base class name of this class. 
   * Should be nonnull for a consistent grammar. */
  private String base = null;

  /** A base class which has has been declared in the grammar.
   *  If {@code baseClass} is {@code null}, {@code base} can be
   *  used to textually represent a class outside the grammar's
   *  context. */
  private AgClass baseClass = null;  

  /** The class members. */
  private List<AgMember> members = new ArrayList<AgMember>(10);
  
  /** The enums defined in this class. */
  public List<AgEnum> enums = new ArrayList<AgEnum>();
  
  /** The (textual) invariants that this class must obey. */
  public List<String> invariants = new ArrayList<String>();
  
  private AgEnum getExistentEnum(String enumName) {
    for (AgEnum e : enums) if (e.name.equals(enumName)) return e;
    return null;
  }

  /** Returns all the members in this class, including the inherited ones.
   * @return {@code getInheritedMembers} concat {@code getSelfMembers}
   */
  public List<AgMember> getMembers() {
    List<AgMember> retv = getInheritedMembers();
    retv.addAll(members);
    return retv;
  }


  /** Returns inherited members.
   * @return a freshly allocated list of members */
  public List<AgMember> getInheritedMembers() {
    return baseClass==null ? 
      new ArrayList<AgMember>(0) : baseClass.getMembers();
  }



  /** Returns members of this class introduced by this class.*/ 
  public List<AgMember> getSelfMembers() {
    return new ArrayList<AgMember>(members);
  }

  /** 
   * Set base class name in the case that there is no base
   * class within the gramma. That is, it should be called
   * only if {@code getBaseClass()==null}; otherwise {@code
   * setBaseClass()} should be used.
   */
  public void setBaseClassName(String name) {
    assert baseClass == null || baseClass.name.equals(name);
    base = name;
  }

  public void setBaseClass(AgClass baseClass) {
    base = baseClass.name;
    this.baseClass = baseClass;
  }

  public String getBaseClassName() {
    return base;
  }

  public AgClass getBaseClass() {
    return baseClass;
  }

  public void addMember(AgMember member) {
    assert !members.contains(member);
    members.add(member);
  }


  
  /**
   * Returns whether an enum with the given name exists already.
   * @param enumName The enum neme to test.
   * @return Whether an enum with that name exists.
   */
  public boolean hasEnum(String enumName) {
    return getExistentEnum(enumName) != null;
  }
  
  /**
   * Returns the enum with a certain name or creates one if none
   * exists. This function does a linear search so it is a good
   * candidate for performance improvement if needed. I don't expect
   * that to be the case because typically a class has at most one enum.
   *  
   * @param enumName the name of the enum
   * @return an {@code AgEnum} object representing the requested enum
   */
  public AgEnum getEnum(String enumName) {
    AgEnum r = getExistentEnum(enumName);
    if (r == null) {
      r = new AgEnum();
      r.name = enumName;
      enums.add(r);
    }
    return r;
  }

  @Override
  public int compareTo(AgClass o) {
    return name.compareTo(o.name);
  }

  @Override
  public boolean equals(Object o) {
    if (!(o instanceof AgClass)) return false;
    return compareTo((AgClass)o) == 0;
  }

  @Override
  public int hashCode() {
    return name.hashCode();
  }
}
