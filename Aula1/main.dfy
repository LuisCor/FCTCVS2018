method Abs(x: int) returns (y: int) 
    ensures (x < 0 && y == -x) || (x >= 0 && y == x)
{
    if x < 0
    { y := -x;}
    else
    { y := x;}

}


method UsingAbs(x:int) {
    var a := Abs(x);
    assert 0 <= a;
    print a;
}


method Min2(x: int, y : int) returns (w:int)
    ensures w == x || w == y
    ensures w <= x && w <= y
{
    if x < y
    {w := x;}
    else
    {w := y;}
}


method Min22(x: int, y : int) returns (w:int)
    ensures x <= y ==> w == x
    ensures x > y ==> w == y
{
    if x < y
    {w := x;}
    else
    {w := y;}
}

/*
method Max3 (x: int, y: int, z : int) returns (w:int)
    ensures w == x || w == y || w == z
    ensures x <= w && y <= w && z <= w
{
    var xy := Max2(x,y);
    assert x <= xy && y <= xy;
    w := Max2(xy,z);
    assert x <= xy && y <= xy;
    assert xy <= w &&  z <= w;
    assert x <= w && y <= w && z <= w;
}
*/


//Especificacao do compareTo usando a limitacao do espaco de resultados
method CompareTo(x:int, y:int) returns (c:int)
    ensures c == 0 || c == 1 || c == -1

{
    if x > y
        { c:= 1;}
    else if x < y
        { c:= -1;}
    else
        {c := 0;}
    
}

//Especificacao do comparaTo usando as comparacoes como factor limitante
method CompareTo2(x:int, y:int) returns (c:int)
    ensures c == 0 <==> x == y
    ensures c == -1 <==> x < y
    ensures c == 1 <==> x > y
{
    if x > y
        { c:= 1;}
    else if x < y
        { c:= -1;}
    else
        {c := 0;}
    
}



//Uso de uma funcao para definir a assercao
function abs(x:int):int
{
    if x < 0 then -x else x
}


method Abs3(x: int) returns (y: int) 
    ensures y == abs(x)
{
    if x < 0
    { y := -x;}
    else
    { y := x;}

}

/*
method swap() {

    var a:=1;
    var b:=2;

    assert a == 1 && b == 2;
    
    var c == 

    assert b == 1 && a == 2;

    a, b := b, a;

    assert a == 1 && b == 2;

}
*/


//proxima aula ciclos e quantificadores
// especificar primeiro os ensures depois desenvolver a funcao


method Max(a:array<int>) returns (m:int)
    requires 0 < a.Length
    ensures forall k : int :: 0 <= k < a.Length ==> a[k] <= m
{
    m := a[0];

    assert forall k : int :: 0 <= k < 1 ==> a[k] <= m;

    var i := 1;
    while i < a.Length
        decreases a.Length-i //todos os ciclos tem que terminar
        invariant 1 <= i <= a.Length
        invariant forall k : int :: 0 <= k < i ==> a[k] <= m
    {
        if m < a[i]
        { m := a[i];} 
        i := i + 1;
    }
    assert forall k : int :: 0 <= k < a.Length ==> a[k] <= m;

}



// complexidade exponencial
function fib(n:int):int 
    requires n >= 0
    decreases n
{
    if n == 0 then 1
    else if n == 1 then 1
    else fib(n-1)+fib(n-2)
}


//Assim usamos a funcao fib com complexidade exponencial para garantir a expecificacao da funcao seguinte sem que seja
//  necessario asserts, para melhorar tempo de execucao. fib e' grantida em compile time e portanto nao tem complexidade exponencial em runtime
method Fib(n:int) returns (f:int)
    requires n >= 0
    ensures f == fib(n)

{
    if n == 0
    {f:=1;}
    else
    {
        var a := 1;
        var b := 1;
        var i := 1;

        while i < n
            decreases n - i
            invariant 1 <= i <= n
            invariant a == fib(i-1)
            invariant b == fib(i)
        {
            a, b := b, a+b;
            i := i + 1;
        }
        f := b;
    }
}