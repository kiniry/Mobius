package bonIDE.diagram.custom;

import java.util.HashMap;

public class ContractFormatter {
	private static HashMap<String, String> unicodeMap = new HashMap<String, String>();

	public ContractFormatter() {
		unicodeMap.put("delta", "\2206");
	}

	public String format(String expressionText) {
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

