method maximRest(suma : int) returns(s : int)
  requires suma > 0
  ensures 0 < s <= suma
  ensures s == 1 || s == 2 || s == 4 || s == 8 || s == 16
  ensures s == 1 ==> suma < 2
  ensures s == 2 ==> 2 <= suma < 4
  ensures s == 4 ==> 4 <= suma < 8
  ensures s == 8 ==> 8 <= suma < 16
  ensures s == 16 ==> 16 <= suma

predicate esteSolutieValida(solutie : seq<int>)
{
  |solutie| == 5 && solutie[0] >= 0 && solutie[1] >= 0 && solutie[2] >= 0 && solutie[3] >=0 && solutie[4] >=0
}

method bancnoteMin(sum: int)returns(sol: seq<int>)
requires sum >=0 
ensures esteSolutieValida(sol)
{
   var rest:=sum;
   var bancnota:=0;
   var s1:=0;
   var s2:=0;
   var s4:=0;
   var s8:=0;
   var s16:=0;
   var s:=0;
   while (0 <rest )
    invariant 0<=rest<=sum
    decreases rest
  {
    //la fiecare iteratie se alege bancnota optima
    // pentru a da rest apoi se modifica solutia
    s:=maximRest(rest);
    if( s ==16)
       { 
        s16:=s16+1;
       }
    else if( s==8)
       { 
        s8:=s8+1;
       }
       else if( s==4)
       { 
        s4:=s4+1;
       }
       else if( s==2)
       { 
        s2:=s2+1;
       } 
       else 
           { s1:=s1+1;}
 
    rest:=rest-s;
  }
     
    sol := [s16, s8, s4, s2, s1];

}

method Main () 
{
  var sum:=47;
  var bancnote:=new int[5];
  bancnote[0],bancnote[1],bancnote[2],bancnote[3],bancnote[4]:=16,8,4,2,1;
  var n:=5; //dimensiunea secventei bancnote
  var sol := bancnoteMin(sum);
  print "Restul optim pentru suma data este = ";
  print "Nr bancnote de 16:";
  print sol[0];
  print "Nr bancnote de 8:";
  print sol[1];
  print "Nr bancnote de 4:";
  print sol[2];
  print "Nr bancnote de 2:";
  print sol[3];
  print "Nr bancnote de 1:";
  print sol[4];
  
}
