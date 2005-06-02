
  private boolean eltsInv(CPair cpair) {
    return (cpair == null ||
            (\typeof(cpair.first) == \type(Pair) &&
             (cpair.second == null) || ((cpair.second instanceof CPair) &&
                                        elts_invariant((CPair)(cpair.second)))));
  }



    // look for pre-existing chain of elements (o, elts)
    for (Pair p = lists; p != null; p = (Pair)(p.second)) {
      List aList = (List)(p.first);
      Pair q = aList.elts;
      if (q.first == o && q.second == elts)
        return q;
    }
    Pair result = Pair.make(o, elts);
    lists = Pair.make(result, lists);
    return result;
