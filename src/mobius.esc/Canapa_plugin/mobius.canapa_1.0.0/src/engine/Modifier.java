package engine;

import input.Suggestion;
import input.intf.SuggestListener;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import jparse.FileAST;
import jparse.Type;
import logs.Log;
import logs.LogType;
import ui.Main;
import canapa.util.FixLocation;
import canapa.util.TreeWalker;

public class Modifier implements SuggestListener {

	Map _files = new HashMap();

	private boolean verifySuggestion(Suggestion suggestion) {
		if (suggestion.getType() == Suggestion.INSTANCE_FIELD
				|| suggestion.getType() == Suggestion.STATIC_FIELD)
			return false;
		return true;
	}

	public void suggest(Suggestion suggestion) {
		if (!verifySuggestion(suggestion)){
			return;
		}
		ModifiedFile file = getFileFromMap(suggestion);
		FileAST fileAST;
		try {
			fileAST = Type.parseFile(file.getFile());
			TreeWalker tw = new TreeWalker(fileAST);
			FixLocation loc = new ModifierFixLocation(suggestion, file);
			boolean found = tw.setAtParamNode(loc);
			if (found) {
				tw.insertJMLbefore(loc.getSuggestion());
				file.increaseOffset(loc);
				file.saveModifications(fileAST);
			} else
				Log.println(LogType.MODIFIER,
						"NIE ZNALEZIONO MIEJSCA GDZIE NALEZALO TO WSTAWIC!!");
		} catch (IOException e) {
			e.printStackTrace();
		}
	}


	private ModifiedFile getFileFromMap(Suggestion suggestion) {
		String fileName = suggestion.getSuggestionLoc().getFile();
		ModifiedFile result = (ModifiedFile) _files.get(fileName);
		if (result == null) {
			result = new ModifiedFile(new File(fileName));
			_files.put(fileName, result);
		}
		return result;
	}

	public void finished() {
		Iterator it = _files.entrySet().iterator();
		Main.saveResults(it);
		selfDestruct(); // ;-)
	}

	private void selfDestruct() {
		_files = new HashMap();
	}

}
