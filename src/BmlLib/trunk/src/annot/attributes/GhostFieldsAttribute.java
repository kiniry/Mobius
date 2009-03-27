package annot.attributes;

import org.antlr.runtime.RecognitionException;

import annot.bcclass.BCClass;
import annot.bcexpression.ExpressionRoot;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents GhostFields class attribute described in "GhostFields
 * Attribute" section of "BML Reference Manual".
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class GhostFieldsAttribute extends ClassAttribute
                                  implements IBCAttribute {

  @Override
  public void parse(String code) throws RecognitionException {
    // TODO Auto-generated method stub
    
  }

  @Override
  protected String printCode1(BMLConfig conf) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public void remove() {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void replace(BCClass bcc) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void replaceWith(BCPrintableAttribute pa) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public String toString() {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public ExpressionRoot[] getAllExpressions() {
    // TODO Auto-generated method stub
    return null;
  }


  public int getIndex() {
    // TODO Auto-generated method stub
    return 0;
  }


  public String getName() {
    // TODO Auto-generated method stub
    return null;
  }


  public void save(AttributeWriter aw) {
    // TODO Auto-generated method stub
    
  }

  @Override
  public void load(AttributeReader ar) throws ReadAttributeException {
    // TODO Auto-generated method stub
    
  }

}
