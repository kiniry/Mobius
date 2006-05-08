package umbra;

import org.eclipse.jface.text.rules.*;

public class TagRule extends MultiLineRule {
	
	int loop = 0;

	public TagRule(IToken token) {
		super("<", ">", token);
	}
	protected boolean sequenceDetected(
		ICharacterScanner scanner,
		char[] sequence,
		boolean eofAllowed) {
		int c = scanner.read();
		if (sequence[0] == '<') {
			if (c == '?') {
				// processing instruction - abort
				scanner.unread();
				return false;
			}
			if (c == '!') {
				//scanner.unread();
				// comment - abort
				//return false;
			}
		} else if (sequence[0] == '>') {
			scanner.unread();
		}
		return super.sequenceDetected(scanner, sequence, eofAllowed);
	}
	
	protected IToken doEvaluate(ICharacterScanner scanner, boolean resume) {
		
		if (resume) {
			
			if (endSequenceDetected(scanner))
				return fToken;
		
		} else {
			
			int c= scanner.read();
			if (c == fStartSequence[0]) {
				if (sequenceDetected(scanner, fStartSequence, false)) {
					loop++;
					int wrong = 0, i = 0;
					while (loop > 0 && loop < 100 && wrong < 100) {
						c = scanner.read();
						i++;
						if (c == fStartSequence[0]) {
							if (sequenceDetected(scanner, fStartSequence, false)) {
								loop++;
								wrong++;
							}	
						}	
						else if (c == fEndSequence[0]) { 
							if (sequenceDetected(scanner, fEndSequence, false)) {
								loop--;
								if (loop == 0) return fToken;
							}	
						}	
					}
					for (; i > 0; i--) scanner.unread();
				}
			}
		}
		
		scanner.unread();
		return Token.UNDEFINED;
	}
}
