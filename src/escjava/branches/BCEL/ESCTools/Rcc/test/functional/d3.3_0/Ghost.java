class GraphData {}

class GraphNode /*#{ghost Object dataLock}*/ {
  GraphData data /*# guarded_by dataLock */;
}

class Graph {
  GraphNode/*#{dataLock}*/[/*#elems_guarded_by this*/] 
    nodes /*#guarded_by this*/;
  final Object dataLock;
}
