package freeboogie.backend.coq;

import java.util.ArrayList;

import freeboogie.backend.Sort;
import freeboogie.backend.TermBuilder;
import freeboogie.backend.coq.representation.CTerm;




/*@ non_null_by_default @*/
/**
 * The back-end for Coq. Works with bicolano. It does not 
 * work with ESC/Java2 right now because it uses the bicolano
 * memory model which ESC/Java2 doesn't.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CoqNodeBuilder extends TermBuilder<CTerm> {


  
  @Override
  protected CTerm reallyMk(Sort sort, String termId, Object a) {
      // TODO Auto-generated method stub
    return  null;
  }

  @Override
  protected CTerm reallyMk(Sort sort, String termId, ArrayList<CTerm> a) {
      // TODO Auto-generated method stub
    return  null;
  }

  @Override
  protected CTerm reallyMkNary(Sort sort, String termId, ArrayList<CTerm> a) {
      // TODO Auto-generated method stub
    return  null;
  }


}
