/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.parser.ast;

import org.antlr.runtime.CommonToken;
import org.antlr.runtime.Token;
import org.antlr.runtime.tree.CommonTreeAdaptor;

public class BONASTNodeAdaptor extends CommonTreeAdaptor {

  @Override
  public Token createToken(Token sourceToken) {
    Token targetToken = super.createToken(sourceToken);

    if (sourceToken instanceof CommonToken && targetToken instanceof CommonToken) {
      CommonToken cSourceToken = (CommonToken)sourceToken;
      CommonToken resultToken = (CommonToken)targetToken;
      resultToken.setStartIndex(cSourceToken.getStartIndex());
      resultToken.setStopIndex(cSourceToken.getStopIndex());
    }
    return targetToken;

  }


}
