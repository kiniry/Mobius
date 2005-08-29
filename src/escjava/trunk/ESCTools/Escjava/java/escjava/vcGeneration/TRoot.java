package escjava.vcGeneration;

/*
 * This class is for the unique root of the tree.
 */
public class TRoot extends TFunction {

  public TRoot(){
    super();
    isroot = true;
  }

  /*
   * As this node is symbolic, it has no sense for the proof.
   * So we just call the functions on the sons.
   */
  /*@ non_null @*/ StringBuffer generateVc(){

    StringBuffer r = new StringBuffer();

    for(int i = 0; i <= sons.size() - 1; i++)
      r.append(getChildAt(i).toDot());
      
    return r;
  }

  /*
   * As this node is symbolic, it should not appear into dot.
   * So we just call on the sons.
   */
    public /*@ non_null @*/ StringBuffer toDot(){

      StringBuffer r = new StringBuffer();

      for(int i = 0; i <= sons.size() - 1; i++)
	r.append(getChildAt(i).toDot());
      
      return r;
    }

}
