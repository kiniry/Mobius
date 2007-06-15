package mobius.directVCGen.vcgen.struct;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javafe.ast.Identifier;

/**
 * An entry to represent the environment of the VCGen
 * @author J. Charles and B. Grégoire
 */
public class VCEntry {
  /** the postcondition of the method */
  public transient Post post;

  /** the exceptional postcondition for the method */
  public transient final Post excpost;
  /** the list of excp post condition; used for the try...catch constructs */
  public transient final List<ExcpPost> lexcpost = new ArrayList<ExcpPost>();

  /** the postcondition for the break, if there is no label */
  public transient Post brpost;
  /** the list of postconditions for breaks in case of labels */
  public transient final Map<Identifier, Post> lbrpost = new HashMap<Identifier, Post>(); 

  /** the postcondition of continue if there is no label */
  public  transient Post contpost;	
  /** the list of postconditions of the continue if there are labels attached to loops */
  public transient final Map<Identifier, Post> lcontpost = new HashMap<Identifier, Post>(); 


  /**
   * The constructor which construct an entry with all the postconditions
   * set to <code>null</code>. It is suspicious. I think it should not be
   * used.
   * @deprecated It is uncoherent to manipulate such an entry. 
   * Maybe it can be used for test.
   */
  public VCEntry () {
    this(null, null, null, null);
  }

  /**
   * Construct a VCEntry in the standard way, from a normal postcondition
   * and an exceptional postcondition.
   * @param post the normal postcondition
   * @param excpost the exceptional postcondition
   */
  public VCEntry(Post post, Post excpost) {
    this(post, excpost, null, null);
  }

  /**
   * Construct a VCEntry from the given elements. The lists have
   * to be initialized directly from the object.
   * @param post the normal postcondition
   * @param excpost the exceptional postcondition
   * @param brpost the postcondition for a break without any label
   * @param contpost the postcondition for a continue without any label
   */
  public VCEntry(Post post, Post excpost, Post brpost, Post contpost) {
    this.post = post;
    this.brpost = brpost;
    this.contpost = contpost;
    this.excpost =  excpost;
  }

  /**
   * Construct a copy of a VCEntry. Basically it copies a reference to 
   * all the fields. For the list of postconditions, it creates new Lists
   * and fill them with the elements of the object being copied.
   * @param ve the object to copy
   */
  public VCEntry(VCEntry ve) {// N OPMD
    post = ve.post;
    brpost = ve.brpost;
    contpost = ve.contpost;
    excpost = ve.excpost;
    lexcpost.addAll(ve.lexcpost);
    lbrpost.putAll(ve.lbrpost);
    lcontpost.putAll(ve.lcontpost);
  }



  /**
   * Uses the constructor {@link #VCEntry(VCEntry)} to construct a clone
   * of the current object.
   */
  public Object clone() {	// N OPMD
    return new VCEntry(this);
  }
}