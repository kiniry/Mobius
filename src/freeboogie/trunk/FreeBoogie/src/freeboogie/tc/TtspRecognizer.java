package freeboogie.tc;

import java.util.*;

import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import genericutils.Closure;
import genericutils.SimpleGraph;

import freeboogie.ast.*;

/**
 * A recognizer for TTSP multidigraphs. See "The recognition
 * of series parallel digraphs" by Valdes, Tarjan, and Lawler.
 *
 * @author rgrig
 * @author reviewed by TODO
 * @param <T> the type of the nodes of the inspected graph
 */
public class TtspRecognizer<T> {
  private final SimpleGraph<T> graph;
  private final T initial;

  private HashMap<T, Integer> toInt = Maps.newHashMap();
  private HashMap<Integer, HashSet<Integer>> pred = Maps.newHashMap();
  private HashMap<Integer, HashSet<Integer>> succ = Maps.newHashMap();
  private HashSet<Integer> todo = Sets.newHashSet();

  public TtspRecognizer(SimpleGraph<T> graph, T initial) {
    this.graph = graph;
    this.initial = initial;
  }
  
  public boolean check() {
    // convert to my representation
    graph.iterNode(new Closure<T>() {
      private int cnt = 0;
      @Override public void go(T n) { toInt.put(n, cnt++); }
    });
    pred.put(-1, new HashSet<Integer>());
    pred.put(-2, new HashSet<Integer>());
    succ.put(-1, new HashSet<Integer>());
    succ.put(-2, new HashSet<Integer>());
    pred.get(-2).add(-1);
    succ.get(-1).add(-2);
    graph.iterNode(new Closure<T>() {
      @Override public void go(T n) {
        HashSet<Integer> p = new HashSet<Integer>();
        pred.put(toInt.get(n), p);
        for (T m : graph.from(n)) p.add(toInt.get(m));
        HashSet<Integer> s = new HashSet<Integer>();
        succ.put(toInt.get(n), s);
        for (T m : graph.to(n)) s.add(toInt.get(m));
        if (s.isEmpty()) {
          s.add(-2);  // final node
          pred.get(-2).add(toInt.get(n));
        }
        if (n == initial) {
          p.add(-1); // initial node
          succ.get(-1).add(toInt.get(n));
        }
        todo.add(toInt.get(n));
      }
    });

    // do reductions
    while (!todo.isEmpty()) {
//System.out.println(todo.size());
      int n = Iterables.get(todo, 0);
      todo.remove(n);
      if (pred.get(n).size() == 1 && succ.get(n).size() == 1) {
        int p = Iterables.get(pred.get(n), 0);
        int s = Iterables.get(succ.get(n), 0);
        succ.get(p).add(s);
        pred.get(s).add(p);
        if (p >= 0) todo.add(p);
        if (s >= 0) todo.add(s);
        succ.remove(n);
        pred.remove(n);
        succ.get(p).remove(n);
        pred.get(s).remove(n);
      }
    }

    // check if we ended up with one edge
//print(pred);
//print(succ);
    assert pred.size() == succ.size();
    return pred.size() == 2;
  }

private static void print(HashMap<Integer,HashSet<Integer>> h) {
  for (Map.Entry<Integer,HashSet<Integer>> e : h.entrySet()) {
    System.out.print("" + e.getKey() + ":");
    for (int x : e.getValue()) System.out.print(" " + x);
    System.out.println();
  }
}

  public static void check(final Program program, final TcInterface tc) {
    program.ast.eval(new Transformer() {
      @Override
      public void see(
        Implementation impl,
        Attribute attr,
        Signature sig, 
        Body body,
        Declaration tail
      ) {
        System.out.print(this + " " + impl.loc() + ": Implementation " + 
          sig.getName() + " SPG check...");
        SimpleGraph<Block> currentFG = tc.getFlowGraph(impl);
        TtspRecognizer<Block> recog = 
          new TtspRecognizer<Block>(currentFG, body.getBlocks());
        if (!recog.check()) {
          System.out.println("FAILED.");
        } else {
          System.out.println("SUCCESS.");
        }
        if (tail != null) tail.eval(this);
      }
    });
  }
}
