package bonIDE.diagram.custom;

import java.util.HashMap;

public class ContractFormatter {
	private static HashMap<String, String> unicodeMap = new HashMap<String, String>();

	public ContractFormatter() {
		unicodeMap.put("delta", "\u2206");
		unicodeMap.put("/=", "\u2260");
		unicodeMap.put(">=", "\u2265");
		unicodeMap.put("<=", "\u2264");
		unicodeMap.put("->", "\u2192");
		unicodeMap.put("<->", "\u2194");
		unicodeMap.put("not", "\u00AC");			
		unicodeMap.put("forall", "\u2200");
		unicodeMap.put("exists", "\u2203");
		unicodeMap.put("memberof", "\u2208");
		unicodeMap.put("nonmemberof", "\u2209");								
		unicodeMap.put("current", "\u0040");
		unicodeMap.put("void", "\u2205");
	}

	public String format(String expressionText) {
		expressionText = expressionText.toLowerCase();
		String[] words = expressionText.split(" ");
		String formattedExp = "";

		for (int wordIdx = 0; wordIdx < words.length; wordIdx++) {
			if (unicodeMap.containsKey(words[wordIdx])) {
				formattedExp += unicodeMap.get(words[wordIdx]);
			} else {
				formattedExp += words[wordIdx];
			}

			// add a space, except at the end
			if (wordIdx < words.length - 1) {
				formattedExp += " ";
			}
		}

		return (formattedExp);
	}
}

