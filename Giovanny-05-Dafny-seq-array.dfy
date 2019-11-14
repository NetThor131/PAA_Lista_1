/*********** QUANTIFICADORES *************

forall x1:T, x2:T2, … xn :Tn | expBool :: expBool

exists x1:T, x2:T2, … xn:Tn | expBool :: expBool

Exemplos

forall x:int :: x*x >=0;
forall x,y | 0 < x <= y :: y / x >= 1;
forall x,y :: 0 < x <= y ==> y / x >= 1;
exists x | 0 <= x < 10 :: x%2 == 0;
exists x :: 0 <= x < 10 && x%2 == 0;

O primeiro exemplo é um for sem guarda.
Dica: tente usar somente for e exists guardados.
*/


/* Solução de exercício:
Implementar o método Fat de tal forma que
a primeira multiplicaçõ de f dentro do loop
seja por n, a seguinte por n-1 e assim sucessivamente
*/

function fat(n:nat) : nat {
    if n == 0
    then 1
    else n * fat(n-1)
}

method Fat(n:nat) returns (f:nat)
ensures f == fat(n)
{
    var i := n;
    f := 1;
    while i > 0
    invariant f * fat(i) == fat(n)
    {
        f := f*i;
        i := i-1;
    }
}

/* Solução de exercício: completar a implementação de Mdc. Use força bruta. */
method Mdc (a:nat, b:nat) returns (m:nat)
requires a > 0 && b > 0
ensures m > 0
ensures a % m == 0 && b % m == 0
ensures forall p | 0 < p :: a % p == 0 && b % p == 0 ==> p <= m
{ m := 1;
  var i:=2;
  while i <= a && i <= b
  invariant forall p | 0 < p < i :: a % p == 0 && b % p == 0 ==> p <= m
  invariant a % m == 0 && b % m == 0
  {
      if a % i == 0 && b % i == 0 {
          m := i;
      }
      i := i+1;
  }
}




/*********Sequencias ou listas (homogéneas)*********

seq<T> é o tipo das sequências de elementos de tipo T

[] sequência vazia
[3, 5, 2, 1, 0, 8] sequência de nat
['a', 'z', '1', 'X'] sequência de characteres

O tipo string equivale com seq<char>.
Assim, também temos que 
['a', 'z', '1', 'X'] é o mesmo que "az1X"

Sequências são homogêneas (os elementos são do mesmo tipo)
[3, 5, 2, 1, 0, 8]: seq<nat>
['a', 'z', '1', 'X']: seq<char>

|s| é o tamanho (número de elementos) da sequência s
|[]| == 0
| [3, 5, 2, 1, 0, 8] | == 6

O operador de concatenação de sequências é o +
[1,2] + [3,1,2] == [1,2,3,1,2]

Verificando se um valor aparece numa sequência
    0 in [2,3,0,4]
    5 !in [2,3,0,4]
	'c' in "abcde"
	'f' !in "abcde"

s[i] é o i-ésimo elemento de s (elemento na posição i)
Posições começam a partir de 0
[3, 5, 2, 1, 0, 8][3] == 1
[3, 5, 2, 1, 0, 8][0] == 3
[3, 5, 2, 1, 0, 8][5] == 5

Slices:
s[i..j]	é a sequência obtida de s tomando os elementos a partir da
        posição j até a posição j-1
        (intervalo fechado à esquerda, aberto à direita).
        Observe que o tamanho é j-i

A primeira posição é a posição 0

Para s[i..j], Dafny exige que
	0 <= i <= j <= |s|

[3, 5, 2, 1, 0, 8][0..2] = [3,5]
[3, 5, 2, 1, 0, 8, 9, 10][3..6] = [1, 0, 8]
"oi pessoal"[0..2] == "oi"


Mais slices 

s[i..]	o substring de s a partir da posiçãoo i até o final

s[..j]	o substring de s desde o início até a posição j-1

s[..]	o próprio s

Mais operações sobre sequências

s1<s2 é true se s1 é um prefixo próprio de s2
s1<=s2 é true se s1 é um prefixo de s2
"abc" < "abcde"
"abc" <= "abc"
[] < [3,20,5,8]
[3,20] < [3,20,5,8]
*/

method MinSeq(a:seq<int>) returns (m:int) 
requires a != []
ensures forall v | v in a :: m <= v
ensures m in a
{
  m := a[0];
  var i:=1;
  while i < |a|
  invariant i <= |a|
  invariant forall k | 0 <= k < i :: m <= a[k]
  invariant m in a
  {
      if a[i] < m {
          m := a[i];
      }
      i := i+1;
  }
}




/************ arrays ********************

Sequência de elementos implementadas eficientemente
  - Mutável
  - Alocado num único bloco contíguo de memória
  - Acesso eficiente (direto) aos elementos

array<t> representa o tipo dos arrays cujos elementos são de tipo t
	var a: array<int> 

Um array de inteiros de n elementos é criado assim
	a := new int[n];

A longitude de um array é dada por
	a.Length 

O i-ésimo elemento (começando por 0 terminando em a.Length-1) é 
	a[i]

Podemos alterar o i-ésimo elemento de a assim
	a[i]:= v;

Uma variável de tipo array contém uma referência, não o array em si
  - pode haver aliasing

o tipos array?<t> permite o valor especial null
  - null expressa ausência de referência 


Arrays vs Sequencias
---------------------

variável tipo array armazena referência
variável tipo seq armazena a sequência completa (Conceitualmente)

arrays são mutáveis
sequências imutáveis

Exemplo:

  a[i] := a[i]+1;     // a alteraçãoo é feita no mesmo array a

  s := s[i:=s[i]+1]; // cria uma nova sequência

  ou

  s := s[..i] + [s[i]+1] + s[i+1..]

Arrays podem ter aliasing
Sequências não (ou aliasing não é perigoso, pois são imutáveis)

Sequências podem ser concatenadas, arrays não

Em geral, seq para especificações, array para implementações


Conversão de array para sequência
----------------------------------

 a[lo..hi]	subarray conversion to sequence
 a[lo..]	drop
 a[..hi]	take
 a[..]		array conversion to sequence


----------------
Especificações precisam definir que variáveis da heap podem ser alteradas
	- Condições sobre *frames*

Num método, tudo aquilo que não é dito que poderá ser alterado permanece igual.

Numa especificaão, old(exp) refere-se ao valor inicial de exp, antes da execução
do corpo do método.
*/


method MinArr(a:array<int>) returns (m:int) 
requires a.Length > 0
ensures forall v | v in a[..] :: m <= v
ensures m in a[..]
{
    m := a[0];
    var i := 1;
    while i < a.Length
    invariant i <= a.Length
    invariant m in a[..]
    invariant forall k | 0 <= k < i :: m <= a[k]
    {
        if a[i] < m {
            m := a[i];
        }
        i := i+1;
    }
}

//Exemplo: somar um aos elementos de uma sequ�ncia
method SomaUm(s:seq<int>) returns (r:seq<int>)
ensures |s| == |r|
ensures forall k | 0 <= k < |s| :: r[k] == s[k] + 1
{
  r:=[];
  var i := 0;
  while i < |s|
  invariant i <= |s|
  invariant |r| == i
  invariant forall k | 0 <= k < i :: r[k] == s[k] + 1
  { 
    r := r + [s[i]+1];
    i := i+1;
  }
}

//Exemplo: somar um aos elementos de um array
method SomaUmArr(a:array<int>)
modifies a
ensures forall k | 0 <= k < a.Length :: a[k] == old(a[k]) + 1
{
  var i := 0;
  while i < a.Length
  invariant i <= a.Length
  invariant forall k | 0 <= k < i :: a[k] == old(a[k]) + 1
  invariant a[i..] == old(a[i..])
  { 
    a[i] := a[i] + 1;
    i := i+1;
  }
}

method Swap(i:nat, j:nat, a:array<int>)
modifies a
requires i < a.Length && j < a.Length
ensures a[i] == old(a[j]) && a[j] == old(a[i])
ensures forall k | 0 <= k < a.Length && k != i && k != j :: a[k] == old(a[k])
{
    a[i], a[j] := a[j], a[i];
}



/**************  Trabalho sugerido ************
ler e fazer os exercícios do tutorial https://rise4fun.com/Dafny/tutorial
*/

// Exercícios (numéricos)
// Min
// Min3
// x^n -- força bruta
// soma dos n primeiros números, por força bruta
// mdc(a,b) de tras pra frente, começando no menor entre a e b.
// mmc
// primo

// Exercícios com arrays
// Dobrar cada um dos elementos de um array de inteiros
// Busca sequêncial
// ****
