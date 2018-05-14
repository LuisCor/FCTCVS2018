

//method a(x:int) returns (y:int)
//  requires -sqrt(2) <= x <= sqrt(2)
//  ensures y <= 2
//{
//  y:=x*x;
//}


method mix(a:array<int>, b:array<int>, m:array<int>, n:int)
modifies m
requires 0 <= n <= a.Length
requires 0 <= n <= b.Length
requires 0 <= 2*n <= m.Length
ensures forall i,k:int :: 0 <= k < 2*n && 0 <= i < n && k%2 == 0 ==> m[k] == a[i]
ensures forall i,k:int :: 0 <= k < 2*n && 0 <= i < n && k%2 == 1 ==> m[k] == b[i]
{
    var i : int := 0;
    var j : int := 0;
    while(i < n)
    decreases n - i
    invariant 0 <= i <= n
    invariant 0 <= j < 2*n
    invariant forall l,k:int :: 0 <= k < j && 0 < l < i && k%2 == 0 ==> m[k] == a[l]
    invariant forall l,k:int :: 0 <= k < j && 0 < l < i && k%2 == 1 ==> m[k] == b[l]

    {
        m[j] := a[i];
        m[j+1] := b[i];
        i := i+1;
        j := j+2;
    }
}



method mirror(a:array<int>, b:array<int>, n:int) returns (r:bool) 
requires 0 <= n <= a.Length
requires 0 <= n <= b.Length

ensures   true ==> forall l : int :: 0 <= l < n ==> a[l] == b[n-1-l]
ensures   false ==> exists l : int :: 0 <= l < n ==> a[l] != b[n-1-l]
{ 
   var i : int := 0; 
   r := true; 

   while(i<n)
   decreases n-i 
   invariant 0 <= i <= n
   invariant r == true ==> forall l : int :: 0 <= l < i ==> a[l] == b[i-1-l]
   invariant r ==  false ==> exists l : int :: 0 <= l < i ==> a[l] != b[i-1-l]
   { 
      if (a[i] != b[n-1-i]) 
         {  
           r := false; 
          } 
      i := i+1; 
   } 
}	



method is_prime(n:int) returns (b:bool) 
requires n >= 0
ensures b <==> forall i::1<i<n ==> n % i != 0
{ 
   var d:int :=2; 
   b := true;

   if (n>1) 
   { 

   while(d<n && b)
   decreases n-d
   invariant d <= n
   invariant b <==> forall l :: 1 < l < d ==> d*l != 0
   { 
      if ( n % d == 0) { b := false ; } 
      d := d + 1; 
   }  
   } 
} 



method IndexOf(a:array<char>, n:int, K:char) returns (pos:int)
requires 0 <= n <= a.Length
ensures -1 <= pos < n
ensures -1 < pos ==> a[pos] == K
ensures pos == -1 ==> forall j:int :: 0 <= j < n ==> a[j] != K
{
    pos := -1;
    var i:int := 0;

    while(i < n)
    decreases n - i
    invariant 0 <= i <= n
    invariant -1 <= pos < i
    invariant -1 < pos ==> a[pos] == K
    invariant pos == -1 ==> forall j:int :: 0 <= j < i ==> a[j] != K
    {
        if (a[i] == K)
        {
            pos := i;
        }
        i:= i+1;
    }
}



method FillK(a:array<char>, n:int, K:char) returns (s:bool)
requires 0 <= n <= a.Length
ensures s <==> forall j:int :: 0 <= j < n ==> a[j] == K
{
    var i:int := 0;
    s := true;
    while(i < n && s == true)
    decreases n - i
    invariant 0 <= i <= n
    invariant s <==> forall j:int :: 0 <= j < i ==> a[j] == K
    {
        if(a[i] != K)
        {
            s := false;
        }
        i := i + 1;
    }
}


method FillKTF(a:array<char>, n:int, K:char) returns (s:bool)
requires 0 <= n <= a.Length
ensures s == true ==> forall j:int :: 0 <= j < n ==> a[j] == K
ensures s == false ==> exists j:int :: 0 <= j < n && a[j] != K
{
    var i:int := 0;
    s := true;
    while(i < n && s == true)
    decreases n - i
    invariant 0 <= i <= n
    invariant s == true ==> forall j:int :: 0 <= j < i ==> a[j] == K
    invariant s == false ==> exists j:int :: 0 <= j < i && a[j] != K
    {
        if(a[i] != K)
        {
            s := false;
        }
        i := i + 1;
    }
}


method FillKExists(a:array<char>, n:int, K:char) returns (s:bool)
requires 0 <= n <= a.Length
ensures !s <==> exists j:int :: 0 <= j < n && a[j] != K
{
    var i:int := 0;
    s := true;
    while(i < n && s == true)
    decreases n - i
    invariant 0 <= i <= n
    invariant !s <==> exists j:int :: 0 <= j < i && a[j] != K
    {
        if(a[i] != K)
        {
            s := false;
        }
        i := i + 1;
    }
}


method Reverse(a:array<int>, n:int) returns (b:array<int>)
requires 0 <= n <= a.Length
ensures a.Length == b.Length
ensures forall j:int :: 0 <= j < n ==> a[j] == b[n-j-1]
ensures forall k:int :: n <= k < a.Length ==> a[k] == b[k]
{
    b:= new int[a.Length];
    
    var i := 0;
    while(i<n)
    decreases n-i
    invariant 0 <= i <= n
    invariant forall j:int :: 0 <= j < i ==> a[j] == b[n-j-1]
    {
        b[n-i-1] := a[i];
        i := i + 1;
    }

    while(i < a.Length)
    decreases a.Length - i
    invariant n <= i <= a.Length
    invariant forall j:int :: 0 <= j < n ==> a[j] == b[n-j-1]
    invariant forall k:int :: n <= k < i ==> a[k] == b[k]
    {
        b[i] := a[i];
        i := i + 1;
    }

} 


function Abs(x: int):int 
    //ensures (x < 0 && y == -x) || (x >= 0 && y == x)
{
    if x < 0 then
    -x
    else
    x

}

method func(x:int, y:int) returns (z:int)
requires Abs(x-y) <= 2
ensures 0 <= z <=2 
//ensures z >= 0 ==> x > y
//ensures x-y <= 2
//ensures y-x <= 2
//ensures x > y ==> z == y-x
//ensures y > x ==> z == x-y
//ensures Abs(z) <= 2
//ensures z != 3
{
    if(x>y)
    {z:=x-y;}
    else
    {z:=y-x;}
}


method Main() {
  print "hello, Dafny\n";
}