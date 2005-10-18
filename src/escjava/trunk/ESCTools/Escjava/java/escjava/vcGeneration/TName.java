package escjava.vcGeneration;

class TName extends TVariable {

    /*@ non_null @*/ String name;

    /*
     * type is supposed to be one of the object that is statically
     * initialized in TNode, like $Reference, $Type etc...
     */
    protected TName(/*@ non_null @*/ String name){
	this.name = name;
    }

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTName(this);
    }


}
