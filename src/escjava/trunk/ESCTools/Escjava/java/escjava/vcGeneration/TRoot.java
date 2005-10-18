package escjava.vcGeneration;

/*
 * This class is for the unique root of the tree.
 */
public class TRoot extends TFunction {

    public TRoot(){
	super();
	isroot = true;
    }

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTRoot(this);
    }
    

}
