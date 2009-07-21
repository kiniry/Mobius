function f(c : name) returns (bool);
const c1 : name;
const c2 : <int>name;
axiom f(c1);
axiom f(c2);

/* New version would look like this:

function f<x>(c : <x>name) returns (bool);
const c1 : <ref>name;
const c2 : <int>name;
axiom f(c1);
axiom f(c2);
*/
