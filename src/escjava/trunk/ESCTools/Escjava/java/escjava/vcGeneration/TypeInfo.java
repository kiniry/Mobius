package escjava.vcGeneration;

class TypeInfo {

  /*
   * README :
   *
   * This class is used to store old types and corresponding new types.
   *
   * If you want to change the way types are renamed, just change 
   * {@link pvsRename} or {@link sammyRename} or add
   * a function at the end.
   */

  /*@ non_null @*/ String old = null;
  private String unsortedPvs  = null;
  private String pvs          = null;
  private String sammy        = null;
	
  public TypeInfo(/*@ non_null @*/ String old){
    this.old = old;
  }

  public /*@ non_null @*/ String getUnsortedPvs(){
    if(unsortedPvs == null)
      unsortedPvsRename();

    return unsortedPvs;
  }

  public /*@ non_null @*/ String getPvs(){
    if(pvs == null)
      pvsRename();

    return pvs;
  }
 
  public /*@ non_null @*/ String getSammy(){
    if(sammy == null)
      sammyRename();

    return sammy;
  }

  public /*@ non_null @*/ String toString(){
    return "["+old+", "+unsortedPvs+", "+pvs+", "+sammy+"]";
  }

  // fixme, does nothing atm
  /*@
   @ ensures unsortedPvs != null;
   @*/
  private void unsortedPvsRename(){
    unsortedPvs = old;
  }


  /*@
   @ ensures pvs != null;
   @*/
  private void pvsRename(){

      // comparison are done in alphabetical order
      if(old.equals("%Type")) // this is the type of a type
	  pvs = "ReferenceType";
      else if(old.equals("boolean"))
	  pvs = "Boolean";
      else if(old.equals("DOUBLETYPE"))
	  pvs = "ContinuousNumber"; //fixme am I right ?
      else if(old.equals("float"))
	  pvs = "ContinuousNumber"; //fixme am I right ?
      else if(old.equals("integer"))
	  pvs = "DiscreteNumber";
      else if(old.equals("INTTYPE")) 
	  pvs = "DiscreteNumber";
      else if(old.equals("null") || old.equals("%Reference"))
	  pvs = "Reference";
      else {
	  System.err.println("Type non handled in escjava::vcGeneration::TypeInfo::pvsRename() : "+old);
	  pvs = old;
      }

  }

  // fixme, does nothing atm
  /*@
   @ ensures sammy != null;
   @*/
  private void sammyRename(){
    sammy = old;
  }
}
