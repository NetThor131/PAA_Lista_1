method Main()
{
   var x:int, y:int;
   ghost var x0, y0 := x, y;
   x := x+y;
   y := x-y;
   x := x-y;
   assert x == y0 && y == x0;
}

method Main1(x:int)
requires x>0; 
{
    var y := x;
    y := y-1; 
    assert y >= 0;
}


method Max(x:int, y:int) returns (z:int)
ensures z >= x && z >= y
ensures z == x || z == y 
{
    if x > y {
        z := x;
    } else {
        z := y;
    }
}

method Max3(x:int, y:int, z:int) returns (r:int)
ensures r >= x && r >= y && r >= z
ensures r == x || r == y || r == z
{
      if x > y && x > z {
          r := x;
      } else if  y > z { //y >= x &&
          r := y;
      } else {
          r:=z;
      }
}

method Mult(m:int, n:int) returns (p:int)
requires n>=0;
ensures p == m*n;
{
  p := 0;
  var i:=0;
  while i < n
  decreases n-i
  invariant p == m*i
  invariant i <= n
  {
      p := p + m;
      i := i+1;
  }
}


method DivMod(m:nat, n:nat) returns (q:nat, r:nat)
requires n !=0
/*ensures r = m%n
ensures q = m/n*/
ensures m == q*n + r
ensures 0 <= r < n
{
      r := m;
      q := 0;
      while r >= n
      invariant m == q*n + r
      {
          r := r - n;
          q := q + 1;
      }
}

function fat(n:nat): nat
{
    if n == 0
    then 1
    else n * fat(n-1)
}

method Fat(n:nat) returns (f:nat)
ensures f == fat(n)
{
    var i := 0;
    f := 1;
    while i < n
    invariant  i <= n
    invariant f == fat(i)
    {
        i := i+1;
        f := i * f;
    }
}

/* Exercício
Implementar o método Fat de tal forma que
a primeira multiplicaçõ de f dentro do loop
seja por n, a seguinte por n-1 e assim sucessivamente
*/

method Mdc(m:nat, n:nat) returns (r:nat)
requires m >0 && n > 0
ensures m % r == 0 && n % r == 0
ensures forall p | p>0 :: m % p == 0 && n % p == 0 ==> p <= r
{

}

/* Exercício, completar a implementação de Mdc acima. Use força bruta. */
