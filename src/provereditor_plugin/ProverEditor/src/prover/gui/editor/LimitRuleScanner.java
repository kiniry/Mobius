package prover.gui.editor;

import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;


public class LimitRuleScanner extends BasicRuleScanner implements IColorConstants {
	private int limit = 0;

	public LimitRuleScanner() {
		this(null);
	}
	
	public LimitRuleScanner(IRule[] rules) {
		super();
		if(rules == null) {
			rules = new IRule[0];
		}
		setRules(rules);
		setDefaultReturnToken(new Token(
			new BasicTextAttribute(DEFAULT_TAG_COLOR)));
	}
	
	
	
	public IToken nextToken() {
		fTokenOffset= fOffset;
		IToken tok = getNextToken(fTokenOffset);
		if(tok.equals(Token.EOF))
			return tok;
		if(fTokenOffset < limit) {
			((BasicTextAttribute)tok.getData()).setBackground(HILIT_COLOR);
		}
		else {
			((BasicTextAttribute)tok.getData()).setBackground(NORMAL_COLOR);
		}
		return tok;
	}
	
	private IToken getNextToken(int off) {
	
		fColumn= UNDEFINED;

		if (fRules != null) {
			for (int i= 0; i < fRules.length; i++) {
				IToken token= (fRules[i].evaluate(this));
				if (!token.isUndefined())
					return token;
			}
		}

		if (read() == EOF)
			return Token.EOF;
		return fDefaultReturnToken;
	}
	
	
	public void setLimit(int l) {
		limit  = l;
	}
	public  int getLimit() {
		return limit;
	}

}
