datatype BinTree = Node(BinTree, int, BinTree) | Leaf

predicate binTree(node: BinTree)
{
  match node
  case Leaf => true
  case Node(left, x, right) =>
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

predicate sorted(a: array<int>, min: int, max: int)
   requires a != null;
   requires 0 <= min <= max < a.Length;
   reads a;
{
  forall j, k :: min <= j < k <= max ==> a[j] <= a[k]
}

predicate sortedSeq(s: seq<int>)
{
  forall j, k :: 0 <= j < k < |s| ==> s[j] <= s[k]
}

function Elements(node: BinTree) : multiset<int>
{
    match node
    case Leaf => multiset([])
    case Node(left, x, right) =>
        Elements(left) + Elements(right) + multiset{x}
}

method Insert(node: BinTree, x: int) returns (ret: BinTree)
    requires binTree(node);
    ensures binTree(ret);
    ensures Elements(ret) == Elements(node) + multiset{x};
{
    match node
    case Leaf =>
        ret := Node(Leaf, x, Leaf);
    case Node(left, data, right) =>
        if (x > data) {
            var newRight := Insert(right, x);
            ret := Node(left, data, newRight);
        }
        else {
            var newLeft := Insert(left, x);
            ret := Node(newLeft, data, right);
        }
}

method Traverse(node: BinTree) returns (ret: seq<int>)
  requires binTree(node);

  ensures sortedSeq(ret);
  ensures Elements(node) == multiset(ret);
{
  match node
  case Leaf =>
    ret := [];
  case Node(left, data, right) =>
    var seqLeft := Traverse(left);
    var seqRight := Traverse(right);

    assert forall i :: 0 <= i < |seqLeft| ==> seqLeft[i] in Elements(left);
    assert forall i :: 0 <= i < |seqRight| ==> seqRight[i] in Elements(right);

    ret := seqLeft + [data] + seqRight;
}

method Sort(a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0;

  ensures multiset(a[..]) == multiset(old(a[..]));
  ensures sorted(a, 0, a.Length - 1);
{
  var i := 0;
  var node := Leaf;

  while (i < a.Length)
  invariant 0 <= i <= a.Length;
  invariant binTree(node);
  invariant forall j :: 0 <= j <= a.Length ==> a[0..j] == old(a[0..j]);
  invariant multiset(old(a[0..i])) == Elements(node);
  {
    node := Insert(node, a[i]);

    i := i + 1;
  }

  assert old(a[0..(a.Length)]) == old(a[..]);

  var sequence := Traverse(node);

  assert |multiset(a[..])| == |sequence|;

  i := 0;

  while (i < |sequence|)
  invariant 0 <= i <= |sequence|;
  invariant 0 <= i <= a.Length;
  invariant a[0..i] == sequence[0..i];
  {
    a[i] := sequence[i];

    i := i + 1;
  }

  assert a[..] == sequence;
}
