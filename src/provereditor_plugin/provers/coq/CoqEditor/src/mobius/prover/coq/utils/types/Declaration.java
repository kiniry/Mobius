package mobius.prover.coq.utils.types;

import org.eclipse.swt.graphics.Image;

import mobius.prover.coq.CoqProverTranslator;
import mobius.prover.gui.editor.ProverEditor;

public class Declaration extends CoqType {

  public Declaration(final ProverEditor editor, 
                     final String name, 
                     final int offset, final int len) {
    super(editor);
    initName(name, offset, len);

  }
  
  public void initName(final String n, 
                       final int offset, final int len) {
    String name = n;
    setOffset(offset);
    setLength(len);
    name = name.trim();
    Image img = null;
    if (name.startsWith("Module")) {
      img = CoqProverTranslator.imgs[1];
      name = name.substring(0, name.length() - 2);
      setLength(len - 2);
    }
    else if (name.startsWith("Declare Module")) {
      img = CoqProverTranslator.imgs[1];
    }
    else if (name.startsWith("Inductive")) {
      img = CoqProverTranslator.imgs[4];
      name = name.substring(0, name.length() - 2);
      setLength(len - 2);
    }
    else if (name.startsWith("Parameter")) {
      img = CoqProverTranslator.imgs[5];
      name = name.substring(0, name.length() - 1);
      setLength(len - 2);
    }
    else if (name.startsWith("Definition")) {
      int i = name.indexOf(":=");
      if (i == -1) {
        i = name.length() - 1;
      }
      name = name.substring(0, i);
      img = CoqProverTranslator.imgs[3];
    }
    else if (name.startsWith("Fixpoint")) {
      int i = name.indexOf(":=");
      if (i == -1) {
        i = name.length() - 1;
      }
      name = name.substring(0, i);
      img = CoqProverTranslator.imgs[8];
    }
    else if (name.startsWith("Record")) {
      int i = name.indexOf(":=");
      if (i == -1) {
        i = name.length() - 1;
      }
      name = name.substring(0, i);
      img = CoqProverTranslator.imgs[9];
    }
    else if (name.startsWith("Let")) {
      int i = name.indexOf(":=");
      if (i == -1) {
        i = name.length() - 1;
      }
      name = name.substring(0, i);
      img = CoqProverTranslator.imgs[10];
    }
    else if (name.startsWith("Scheme")) {
      name = name.substring(0, name.length() - 2);
      img = CoqProverTranslator.imgs[6];
      setLength(len - 2);
    }
    else {
      img = CoqProverTranslator.imgs[7];
    }
    setName(name.trim());
    setImage(img);
  }


}
