datatype Label = Red | Black
datatype RBTree = Node(Label, RBTree, int, RBTree) | Leaf

predicate rbTree(node: RBTree)
{
  match node
  case Leaf => true
  case Node(lbl, left, data, right) =>
    match lbl
    case Red =>
      rbTree(left) &&
      rbTree(right) &&
      isBlack(left) &&
      isBlack(right) &&
      blackHeight(left) == blackHeight(right) &&
      leqThan(left, data) &&
      geqThan(right, data)
    case Black =>
      rbTree(left) &&
      rbTree(right) &&
      blackHeight(left) == blackHeight(right) &&
      leqThan(left, data) &&
      geqThan(right, data)

}

predicate quasiRbTree(node: RBTree)
{
  match node
  case Leaf => true
  case Node(lbl, left, data, right) =>
    rbTree(left) &&
    rbTree(right) &&
    blackHeight(left) == blackHeight(right) &&
    leqThan(left, data) &&
    geqThan(right, data)
}

function blackHeight(node: RBTree) : int
{
  match node
    case Leaf => 1
    case Node(lbl, left, data, right) =>
      match lbl {
      case Red => max(blackHeight(left), blackHeight(right))
      case Black => 1 + max(blackHeight(left), blackHeight(right))
      }
}

predicate isBlack(node: RBTree)
{
  match node
  case Leaf => true
  case Node(lbl, _, _, _) =>
    match lbl
    case Black => true
    case Red => false
}

predicate leqThan(node: RBTree, num: int)
{
  forall y :: (y in Elements(node)) ==> y <= num
}

predicate geqThan(node: RBTree, num: int)
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

function max(a: int, b: int) : int
{
  if a > b then a else b
}

function Elements(node: RBTree) : multiset<int>
{
  match node
  case Leaf => multiset{}
  case Node(lbl, left, data, right) =>
    Elements(left) + multiset{data} + Elements(right)
}

lemma leqMember(nodex: int, node: RBTree, y: int)
  requires leqThan(node, y);
  requires nodex in Elements(node);

  ensures nodex <= y;
{
}

lemma geqMember(nodex: int, node: RBTree, y: int)
  requires geqThan(node, y);
  requires nodex in Elements(node);

  ensures nodex >= y;
{
}

method Balance_LRed_RBlack_LLBlack(ll: RBTree, lx: int, lr: RBTree, data: int, r: RBTree) returns (ret: RBTree) // ret = r + 1
  requires rbTree(ll);
  requires rbTree(lr);
  requires rbTree(r);
  requires blackHeight(ll) == blackHeight(r);
  requires blackHeight(lr) == blackHeight(r);
  requires leqThan(ll, lx);
  requires geqThan(lr, lx);
  requires lx <= data;
  requires leqThan(lr, data);
  requires geqThan(r, data);
  requires isBlack(ll);

  ensures Elements(ret) == Elements(ll) + multiset{lx} + Elements(lr) +
    multiset{data} +
    Elements(r);
  ensures rbTree(ret);
  ensures blackHeight(ret) == (blackHeight(r) + 1);
{
  var l := Node(Red, ll, lx, lr);

  match lr {
  case Node(lrLbl, lrl, lrx, lrr) =>
    match lrLbl {
    case Red => // Case 3: Left is red, right is black, left left is black, left right is red
          // Result: ret is red, right and left are black (rotated)
      var newLeft := Node(Black, ll, lx, lrl);
      var newRight := Node(Black, lrr, data, r);

      assert Elements(lrl) <= Elements(lr);
      assert Elements(lrr) <= Elements(lr);

      ret := Node(Red, newLeft, lrx, newRight);
    case Black => // Case 4: Left is red, right is black, left left is black, left right is black
            // Result: ret is black
      ret := Node(Black, l, data, r);
    }
  case Leaf =>
    ret := Node(Black, l, data, r);
  }
}

method Balance_LRed_RBlack(ll: RBTree, lx: int, lr: RBTree, data: int, r: RBTree) returns (ret: RBTree) // ret = r + 1
  requires rbTree(ll);
  requires rbTree(lr);
  requires rbTree(r);
  requires blackHeight(ll) == blackHeight(r);
  requires blackHeight(lr) == blackHeight(r);
  requires leqThan(ll, lx);
  requires geqThan(lr, lx);
  requires lx <= data;
  requires leqThan(lr, data);
  requires geqThan(r, data);
  requires isBlack(r);

  ensures Elements(ret) == Elements(ll) + multiset{lx} + Elements(lr) +
    multiset{data} +
    Elements(r);
  ensures rbTree(ret);
  ensures blackHeight(ret) == (blackHeight(r) + 1);
{
  var left := Node(Red, ll, lx, lr);

  match ll {
  case Node(llLbl, lll, llx, llr) =>
    match llLbl {
    case Red => // Case 2: Left is red, right is black, left left is red.
          // Result: ret is red, right and left are black (rotated)
      var newLeft := Node(Black, lll, llx, llr);
      var newRight := Node(Black, lr, data, r);

      ret := Node(Red, newLeft, lx, newRight);
    case Black =>
      ret := Balance_LRed_RBlack_LLBlack(ll, lx, lr, data, r);
    }
  case Leaf =>
    ret := Balance_LRed_RBlack_LLBlack(ll, lx, lr, data, r);
  }
}

method Balance_LBlack_RRed(l: RBTree, data: int, rl: RBTree, rx: int, rr: RBTree) returns (ret: RBTree)
  requires rbTree(l);
  requires rbTree(rl);
  requires rbTree(rr);
  requires blackHeight(l) == blackHeight(rl);
  requires blackHeight(rl) == blackHeight(rr);
  requires leqThan(l, data);
  requires geqThan(rl, data);
  requires rx >= data;
  requires leqThan(rl, rx);
  requires geqThan(rr, rx);

  ensures Elements(ret) == Elements(l) +
    multiset{data} +
    Elements(rl) + multiset{rx} + Elements(rr);
  ensures rbTree(ret);
  ensures blackHeight(ret) == (blackHeight(l) + 1);
{
  var r := Node(Red, rl, rx, rr);

  match rl {
  case Node(rlLbl, rll, rlx, rlr) =>
    match rlLbl {
    case Red => // Case 5: Left is black, right is red, right left is red
          // Result: ret is red, right and left are black (rotated)
      var newLeft := Node(Black, l, data, rll);
      var newRight := Node(Black, rlr, rx, rr);

      assert Elements(rll) <= Elements(rl);
      assert Elements(rlr) <= Elements(rl);

      ret := Node(Red, newLeft, rlx, newRight);
    case Black =>
      ret := Balance_LBlack_RRed_RLBlack(l, data, rl, rx, rr);
    }
  case Leaf =>
    ret := Balance_LBlack_RRed_RLBlack(l, data, rl, rx, rr);
  }
}

method Balance_LBlack_RRed_RLBlack(l: RBTree, data: int, rl: RBTree, rx: int, rr: RBTree) returns (ret: RBTree)
  requires rbTree(l);
  requires rbTree(rl);
  requires rbTree(rr);
  requires blackHeight(l) == blackHeight(rl);
  requires blackHeight(rl) == blackHeight(rr);
  requires leqThan(l, data);
  requires geqThan(rl, data);
  requires rx >= data;
  requires leqThan(rl, rx);
  requires geqThan(rr, rx);
  requires isBlack(rl);

  ensures Elements(ret) == Elements(l) +
    multiset{data} +
    Elements(rl) + multiset{rx} + Elements(rr);
  ensures rbTree(ret);
  ensures blackHeight(ret) == (blackHeight(l) + 1);
{
  var r := Node(Red, rl, rx, rr);

  match rr {
  case Node(rrLbl, rrl, rrx, rrr) =>
    match rrLbl {
    case Red => // Case 6: Left is black, right is red, right left is black, right right is red
          // Result: ret is red, right and left are black (rotated)
      var newLeft := Node(Black, l, data, rl);
      var newRight := Node(Black, rrl, rrx, rrr);

      assert Elements(rrl) <= Elements(rr);
      assert Elements(rrr) <= Elements(rr);

      ret := Node(Red, newLeft, rx, newRight);
    case Black => // Case 4: Left is black, right is red, right left is black, right right is black
            // Result: ret is black
      ret := Node(Black, l, data, r);
    }
  case Leaf =>
    ret := Node(Black, l, data, r);
  }
}

method Balance(l: RBTree, data: int, r: RBTree) returns (ret: RBTree)
  requires quasiRbTree(l);
  requires quasiRbTree(r);
  requires leqThan(l, data);
  requires geqThan(r, data);
  requires blackHeight(l) == blackHeight(r);

  ensures Elements(ret) == Elements(l) + multiset{data} + Elements(r);
  ensures rbTree(ret);
  ensures blackHeight(ret) == (blackHeight(r) + 1);
{
  match l {
  case Node(llbl, ll, lx, lr) =>
    leqMember(lx, l, data);
    assert forall j :: j in Elements(lr) ==> j in Elements(l);
    match r {
    case Node(rlbl, rl, rx, rr) =>
      geqMember(rx, r, data);
      assert forall j :: j in Elements(rl) ==> j in Elements(r);
      match llbl {
      case Red =>
        match rlbl {
        case Red => // Case 1: Both left and right are red
              // Result: ret is red, left and right are black
          var newLeft := Node(Black, ll, lx, lr);
          var newRight := Node(Black, rl, rx, rr);

          ret := Node(Red, newLeft, data, newRight);
        case Black =>
          ret := Balance_LRed_RBlack(ll, lx, lr, data, r);
        }
      case Black =>
        match rlbl {
        case Red =>
          ret := Balance_LBlack_RRed(l, data, rl, rx, rr);
        case Black => // Case 4: Left is black, right is black
          ret := Node(Black, l, data, r);
        }
      }
    case Leaf =>
      match llbl {
      case Red =>
        ret := Balance_LRed_RBlack(ll, lx, lr, data, r);
      case Black =>
        ret := Node(Black, l, data, r);
      }
    }
  case Leaf =>
    match r {
    case Node(rlbl, rl, rx, rr) =>
      geqMember(rx, r, data);
      assert forall j :: j in Elements(rl) ==> j in Elements(r);
      match rlbl {
      case Red =>
        ret := Balance_LBlack_RRed(l, data, rl, rx, rr);
      case Black => // Case 4: Left is black, right is black
        ret := Node(Black, l, data, r);
      }
    case Leaf => // Case 4: Left is black, right is black
      ret := Node(Black, l, data, r);
    }
  }
}

method InsertAux(node: RBTree, x: int) returns (ret: RBTree)
  requires rbTree(node);
  ensures quasiRbTree(ret);
  ensures Elements(ret) == Elements(node) + multiset{x};
  ensures blackHeight(node) == blackHeight(ret);
  ensures isBlack(node) ==> rbTree(ret);
{
  match node
  case Leaf =>
    ret := Node(Red, Leaf, x, Leaf);
  case Node(lbl, left, data, right) =>
    match lbl
    case Black =>
      if (x <= data) {
        var newLeft := InsertAux(left, x);

        ret := Balance(newLeft, data, right);
      }
      else {
        var newRight := InsertAux(right, x);

        ret := Balance(left, data, newRight);
      }
    case Red =>
      if (x <= data) {
        var newLeft := InsertAux(left, x);

        ret := Node(Red, newLeft, data, right);
      }
      else {
        var newRight := InsertAux(right, x);

        ret := Node(Red, left, data, newRight);
      }
}

method Insert(node: RBTree, x: int) returns (ret: RBTree)
  requires rbTree(node);
  ensures rbTree(ret);
  ensures Elements(ret) == Elements(node) + multiset{x};
{
  var newNode := InsertAux(node, x);

  match newNode
  case Leaf =>
    ret := Leaf;
  case Node(lbl, left, data, right) =>
    ret := Node(Black, left, data, right);
}

method Traverse(node: RBTree) returns (ret: seq<int>)
  requires rbTree(node);

  ensures sortedSeq(ret);
  ensures Elements(node) == multiset(ret);
{
  match node
  case Leaf =>
    ret := [];
  case Node(lbl, left, data, right) =>
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
  invariant rbTree(node);
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
