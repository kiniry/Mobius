package b2bpl.bpl.ast;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;


public abstract class BPLCommentableNode extends BPLNode {

  private final List<String> comments = new ArrayList<String>();

  public final void addComment(String comment) {
    comments.addAll(Arrays.asList(comment.split("\n")));
  }

  public final String[] getComments() {
    return comments.toArray(new String[comments.size()]);
  }

  public final void clearComments() {
    comments.clear();
  }
}
