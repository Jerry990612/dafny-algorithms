predicate sorted(a: array<int>, min: int, max: int)
   requires a != null;
   requires 0 <= min <= max < a.Length;
   reads a;
{
  forall j, k :: min <= j < k <= max ==> a[j] <= a[k]
}

predicate heap(a: array<int>, max: int)
  requires a != null;
  requires 0 <= max < a.Length;
  reads a;
{
  forall i :: 0 < i <= max ==> a[(i - 1) / 2] >= a[i]
}

predicate heapExceptJParent(a: array<int>, i: int, j: int)
  requires a != null;
  requires 0 <= i < a.Length;
  requires 0 <= j < a.Length;
  reads a;
{
  (forall k :: 0 < k <= i && k != j ==> a[(k - 1) / 2] >= a[k]) &&
          (forall k :: 0 < k <= i && (k - 1) / 2 == j && j > 0 ==>
            a[((k - 1) / 2 - 1) / 2] >= a[k])
}

predicate heapExceptJChildren(a: array<int>, i: int, j: int)
  requires a != null;
  requires 0 <= i < a.Length;
  requires 0 <= j < a.Length;
  reads a;
{
  (forall k :: 0 < k <= i && ((k - 1) / 2) != j ==> a[(k - 1) / 2] >= a[k]) &&
    (forall k :: 0 < k <= i && (k - 1) / 2 == j && j > 0 ==>
      a[((k - 1) / 2 - 1) / 2] >= a[k])
}

predicate max(a: array<int>, i: int, j: int)
  requires a != null;
  requires 0 <= j <= i < a.Length;
  reads a;
{
  forall k :: 0 <= k <= i ==> a[k] <= a[j]
}

lemma heapMax(a: array<int>, i: int)
  requires a != null;
  requires 0 <= i < a.Length;
  requires heap(a, i);
  ensures forall k :: 0 < k <= i ==> a[0] >= a[k];
  ensures max(a, i, 0);
{
  var j := 1;

  while (j <= i)
  invariant j > 0;
  invariant forall x :: 0 < x < j && x <= i ==> a[0] >= a[x];
  {
    var k := j;

    while (k > 0)
    invariant 0 <= k <= j <= i;
    invariant a[k] >= a[j];
    {
      k := (k - 1) / 2;
    }

    j := j + 1;
  }
}

method Swap(a: array<int>, i: int, j: int)
  modifies a;
  requires a != null;
  requires 0 <= i < j < a.Length;
  ensures a[i] == old(a[j]);
  ensures a[j] == old(a[i]);
  ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m]);
  ensures multiset(a[..]) == old(multiset(a[..]));
{
  a[i], a[j] := a[j], a[i];
}

method Heapify(a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0;
  ensures heap(a, a.Length - 1);
  ensures multiset(a[..]) == multiset(old(a[..]));
{
  var i := 1;

  while (i < a.Length)
  invariant 0 < i <= a.Length;
  invariant heap(a, i - 1);
  invariant multiset(a[..]) == multiset(old(a[..]));
  {
    var j := i;

    while (j > 0 && a[(j - 1) / 2] < a[j]) // Bubble up
    invariant 0 <= j <= i;
    invariant heapExceptJParent(a, i, j);
    invariant multiset(a[..]) == multiset(old(a[..]));
    {
      Swap(a, (j - 1) / 2, j);
      j := (j - 1) / 2;
    }

    i := i + 1;
  }
}

method UnHeapify(a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0;
  requires heap(a, a.Length - 1);
  ensures multiset(a[..]) == multiset(old(a[..]));
  ensures sorted(a, 0, a.Length  - 1);
{
  var i := a.Length - 1;

  heapMax(a, i);

  while (i > 0)
  invariant a != null;
  invariant a.Length > 0;
  invariant 0 <= i < a.Length;
  invariant heap(a, i);
  invariant sorted(a, i, a.Length  - 1);
  invariant multiset(a[..]) == multiset(old(a[..]));
  invariant max(a, i, 0);
  invariant forall x :: 0 <= x <= i && i < (a.Length - 1) ==> a[x] <= a[i + 1]
  {
    heapMax(a, i);
    Swap(a, 0, i);

    var j := 0;

    while (j < (i / 2))
    invariant 0 <= j <= i < a.Length;
    invariant heapExceptJChildren(a, i - 1, j);
    invariant multiset(a[..]) == multiset(old(a[..]));
    invariant forall x :: 0 <= x <= i ==> a[x] <= a[i];
    invariant sorted(a, i, a.Length  - 1);
    {
      var left := j * 2 + 1;
      var right := j * 2 + 2;
      var largest := j;

      if (right < i && a[right] > a[largest]) {
        largest := right;
      }
      if (left < i && a[left] > a[largest]) {
        largest := left;
      }
      if (largest != j) {
        Swap(a, j, largest);
        j := largest;
      }
      else {
        break;
      }
    }

    i := i - 1;
    heapMax(a, i);
  }
}

method HeapSort(a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0
  ensures multiset(a[..]) == multiset(old(a[..]));
  ensures sorted(a, 0, a.Length - 1);
{
  Heapify(a);
  UnHeapify(a);
}
