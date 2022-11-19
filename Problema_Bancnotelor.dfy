method BancnoteMin(sum: int, n: int, bancnote: array<int>,sol: array<int>)
modifies sol
requires sum >= 0
{
  /*
  suma initiala, suma de dat ca rest care trebuie construita, 
  rest=suma;
  for(int i=0;i<n;i++)
    {
      while(rest>bancnote[i])
      {
        rest=rest-bancote[i];
        sol[i]++;
      }
    }
  */
   var rest:=sum;
   var i:=0;
   while i< n-1
    invariant 0 <= i <=n-1
    decreases n-i
  {
    while  bancnote[i]<rest
    invariant 0 <= bancnote[i] <=rest
    {
      rest:=rest-bancnote[i];
      sol[i]:=sol[i]+1;
    }
    i:=i+1;
  }   

}

method Main () 
{
  var sum:=47;
  var bancnote:=new int[5];
  bancnote[0],bancnote[1],bancnote[2],bancnote[3],bancnote[4]:=16,8,4,2,1;
  var n:=5; //dimensiunea secventei bancnote
  var sol:=new int[5];
  sol[0],sol[1],sol[2],sol[3],sol[4]:=0,0,0,0,0;
  BancnoteMin(sum,n,bancnote,sol);
  print "Restul optim pentru suma data este = ";
  var i:int :=0;
  while i< n-1 
    invariant 0 <= i<n
    decreases n-i
  {
    while 0 < sol[i] 
      invariant 0<=sol[i]<=sol[i]
      decreases sol[i]
      {
        print sol[i];
        print " ";
        sol[i]:=sol[i]-1;
      }
    i:=i+1;
  }
  //ar trebui sa afiseze "16 16 8 4 2 1"
}