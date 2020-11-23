/* Homework 02b:

 Implement the following program and prove its correctness using Dafny:
 https://rise4fun.com/Dafny

*/
function mul(n: nat, m: nat): int
  requires n >= 0 && m >= 0;
  {
    n * m
  }
// You can add some auxiliary variables 
// but do not change the code computing a, b, and x.

//My notes: I really do not know, how to prove b is decreasing... except that I guess invariants should be fine, maybe there could be some stronger one in first one?
method Multiply(N: int, M: nat) returns (R: int)
  ensures R == M*N;
  requires N>=0 && M>=0;
{
  var a := N;
  var b := M;
  var x := 0;
  while (b > 0)
  
  decreases b;
  invariant x == R - (b * a);
  //invariant b != 0 ==> a == (R - x) / b;
  //invariant a != 0 ==> b == (R - x) / a;
  {
    while (b % 10 != 0)
    decreases (b % 10);
    decreases b;
    invariant x == R - (b * a);
    {
      x := x + a;
      b := b - 1;
    }
    a := 10 * a;
    b := b / 10;
  }
  R := x;
}