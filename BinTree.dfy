datatype BinTree = Node(BinTree, BinTree, int) | Leaf

predicate binTree(node: BinTree)
{
  match node
  case Leaf => true
  case Node(left, right, x) =>
      binTree(left) &&
      binTree(right) &&
      leqThan(left, x) &&
      geqThan(right, x)
}

predicate leqThan(node: BinTree, num: int)
{
    forall y :: (y in Elements(node)) ==> y <= num
}

predicate geqThan(node: BinTree, num: int)
{
    forall y :: (y in Elements(node)) ==> y >= num
}

function Elements(node: BinTree) : multiset<int>
{
    match node
    case Leaf => multiset([])
    case Node(left, right, x) =>
        Elements(left) + Elements(right) + multiset{x}
}

method Insert(node: BinTree, x: int) returns (ret: BinTree)
    requires binTree(node);
    ensures binTree(ret);
    ensures Elements(ret) == Elements(node) + multiset{x};
{
    match node
    case Leaf =>
        ret := Node(Leaf, Leaf, x);
    case Node(left, right, data) =>
        if (x > data) {
            var newRight := Insert(right, x);
            ret := Node(left, newRight, data);
        }
        else {
            var newLeft := Insert(left, x);
            ret := Node(newLeft, right, data);
        }
}
