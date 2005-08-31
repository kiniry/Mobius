package escjava.vcGeneration;

class VariableInfo {

    /*
     * README :
     *
     * This class is used to contain renaming of variables.
     * For each variable a VariableInfo object is created.
     *
     * If you want to change the way variables are renamed, just change 
     * {@link pvsRename} or {@link sammyRename} or add
     * a function at the end.
     */
  
    /*@ non_null @*/ String     oldName = null;
    TypeInfo                       type = null;
    private String unsortedPvsName      = null;
    private String pvsName              = null;
    private String sammyName            = null;
    public boolean typeSure             = false;
	
    /*
     * When we call this variable, we know his old type, so we gave it.
     */
    public VariableInfo(/*@ non_null @*/ String oldName, TypeInfo type){
	this.oldName = oldName;
	this.type = type;
    }

    public /*@ non_null @*/ String getUnsortedPvsName(){
	if(unsortedPvsName == null)
	    unsortedPvsRename();

	return unsortedPvsName;
    }

    public /*@ non_null @*/ String getPvsName(){
	if(pvsName == null)
	    pvsRename();

	return pvsName;
    }
 
    public /*@ non_null @*/ String getSammyName(){
	if(sammyName == null)
	    sammyRename();

	return sammyName;
    }

    public /*@ non_null @*/ String toString(){
	return "["+oldName+", "+type+", "+pvsName+", "+sammyName+"]";
    }

    // fixme, does nothing atm
    /*@
      @ ensures unsortedPvsName != null;
      @*/
    private void unsortedPvsRename(){
	unsortedPvsName = oldName;
    }

    // fixme, does nothing atm
    /*@
      @ ensures pvsName != null;
      @*/
    private void pvsRename(){
	pvsName = oldName;
    }

    // fixme, does nothing atm
    /*@
      @ ensures sammyName != null;
      @*/
    private void sammyRename(){
	sammyName = oldName;
    }
}
