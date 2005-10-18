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

    /*
     * Constructor for specifying the renaming of the type.
     */
  public TypeInfo(/*@ non_null @*/ String old, /*@ non_null @*/ String unsortedPvs, /*@ non_null @*/ String pvs, /*@ non_null @*/ String sammy){
    this.old = old;
    this.unsortedPvs = unsortedPvs;
    this.pvs = pvs;
    this.sammy = sammy;
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

      if(old.equals("null") )
	  pvs = "Reference";
      else {
	  // common rules here //fixme, be more specific maybe
	  if(old.startsWith("java.")) //check if in the form java.x.y 
	      pvs = old.replace('.','_');
	  else {
	      TDisplay.warn(this, "pvsRename()", "Type not handled  : "+old); 
	      TDisplay.warn(this, "pvsRename()", "Considering it as a user defined type... ie ReferenceType");
	      pvs = "ReferenceType";
	  }
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
