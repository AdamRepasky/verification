/* Homework 02a:

 Implement the following program and prove its correctness using Dafny:
 https://rise4fun.com/Dafny

*/

function OddProduct(a: array<int>, from: nat) : int
    reads a
    requires a != null
    requires from <= a.Length
    decreases a.Length-from
{
    if from == a.Length then 1
    else if (from % 2 == 0) then OddProduct(a, from + 1)
    else a[from] * OddProduct(a, from + 1)
}
function EvenSum(a: array<int>, from: nat) : int
    reads a
    requires a != null
    requires from <= a.Length
    decreases a.Length-from
{
    if from == a.Length then 0
    else if (from % 2 == 1) then EvenSum(a, from + 1)
    else a[from] + EvenSum(a, from + 1)
}

method compute(A: array<int>) 
  returns (E: int, O: int, M: int)
  // Implement this method such that: 
  //  - E is the sum of all even numbers of A
  //  - O is the product of all odd numbers of A
  //  - M is the maximal number of A
  // When A is an empty array, the result should be (0, 1, 8).
  // Yes, M for an empty array should be 8 (there is no -infty in Dafny).
  // Add invariants, ensures, requires, (functions)... s.t. Dafny can prove the correctness.
    requires A != null
    ensures O == OddProduct(A, 0)
    ensures E == EvenSum(A, 0)
    ensures (forall j :int :: (j >= 0 && j < A.Length ==> M >= A[j]));
    ensures (A.Length > 0)==>(exists j : int :: j>=0 && j < A.Length && M==A[j]);
{
    var i : nat;
    E, O, i := 0, 1, 0;

    ghost var r := OddProduct(A,0);
    ghost var s := EvenSum(A,0);
    
    if (A.Length == 0) {
      M := 8;
    }
    else {
      M:=A[0];
      while (i < A.Length)
          invariant i <= A.Length
          decreases (A.Length-i);
          
          //assuming we index from 0 => first element is at even space
          invariant O * OddProduct(A,i) == r
          invariant E + EvenSum(A,i) == s
          
          //for maximum
          invariant forall j:: 0<=j<i ==> A[j] <= M;
          invariant i!=0 ==> exists j:: 0<=j<i && A[j]==M;
          invariant i==0 ==> A[0] >= M;
          
      {   
        if (i % 2 == 0) {
          E := E + A[i];
        } else {
          O := O * A[i];
        }
        M := if (A[i] > M) then A[i] else M;
        i := i + 1;
      }
    }
}