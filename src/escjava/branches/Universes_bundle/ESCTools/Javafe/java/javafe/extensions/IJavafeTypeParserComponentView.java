package javafe.extensions;

import javafe.ast.Expr;
import javafe.ast.Type;
import javafe.parser.Lex;

public interface IJavafeTypeParserComponentView {

	public void initForPragmaModifiers();
	
	public boolean parsePragmaModifiers(/*@ non_null @*/ Lex l, 
			                            boolean inDeclaration);
	
	public boolean parseKeywordModifiers(/*@ non_null @*/ Lex l,
										 boolean inDeclaration);

	public boolean parseInstanceofTypeInformation(/*@ non_null @*/ Lex l);

	public void assignTypeInformation(/*@ non_null @*/ Expr e, 
									  /*@ non_null @*/ Type t, int loc);
}
