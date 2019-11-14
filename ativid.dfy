// 1 - 
method maior(x: int, y: int) returns (z: int)
ensures z >= x && z >= y
ensures z == x || z == y
{
    if x >= y
        { z := x; }
    else
        { z := y; } 
}

// 2 -
method maior3(x: int, y: int, z: int) returns (maior: int)
ensures maior >= x && maior >= y && maior >= z
ensures maior == x || maior == y || maior == z
{
    if (x >= y && x >= z)
        { maior := x; }
    else
        {
            if (y >= x && y >= z)
                { maior := y; }
            else
                { maior := z; }
        }
}

// 3 -
method eleva(x: int, n: int) returns (r: int)
requires n >= 0 
{
    var aux := n;
    r := x;
    while aux > 0
    decreases aux
    {
        r := r * x;
        aux := aux - 1;
    }
}

// 4 -
method somaate(x: int) returns (r: int)
requires x >= 0
{
    r := 0;
    var aux := 0;
    while aux < x
    decreases x - aux
    {
        r := r + aux;
        aux := aux + 1;
    }
}

// 5 - Para calcular o maximo comum divisor (mdc) de 'a' e 'b', 
// escreva um metodo que inicia no menor entre 'a' e 'b', vai 
// decrementando em um a cada passo, e termina quando encontra 
// o primeiro numero que divide tanto a 'a' como a 'b'.
method mdc(a: int, b: int) returns (mdc: int)
requires a > 0 && b > 0
ensures mdc % a == 0 && mdc % b == 0
ensures mdc <= a && mdc <= b
{
    if a <= b
        { mdc := a; }
    else
        { mdc := b; }
    while mdc > 0
    decreases mdc
    {
        if mdc % a == 0 && mdc % b == 0
            { return mdc; }
        else
            { mdc := mdc - 1; }
    }   
}

// 6 - Utilizando forca bruta, calcule o mınimo multipo comum de dois naturais.
method mmc(a: nat, b: nat) returns (mmc: nat)
{
    if a >= b
        { mmc := a; }
    else
        { mmc := b; }
    while mmc 
}
