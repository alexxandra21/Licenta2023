function nrBancnoteSol(solutie : seq<int>): int
requires esteSolutieValida(solutie)
{
  solutie[0] + solutie[1] +  solutie[2] + solutie[3] + solutie[4]
}

function sumSolutii(s1 : seq<int>,s2 : seq<int>): seq<int>
requires esteSolutieValida(s1)
requires esteSolutieValida(s2)
{
  [s1[0]+s2[0], s1[1]+s2[1], s1[2]+s2[2], s1[3]+s2[3],s1[4]+s2[4]]
}

method maximRest(suma : int) returns(s : int)
  requires suma > 0
  ensures 0 < s <= suma
  ensures s == 1 || s == 2 || s == 4 || s == 8 || s == 16
  ensures s == 1 ==> suma < 2
  ensures s == 2 ==> 2 <= suma < 4
  ensures s == 4 ==> 4 <= suma < 8
  ensures s == 8 ==> 8 <= suma < 16
  ensures s == 16 ==> 16 <= suma
  {
    if( 16 <= suma )
     {
      s:=16;
     }
     else if(8 <= suma)
     {
      s:=8;
     }
    else if(4 <= suma)
     {
      s:=4;
     }
    else if(2 <= suma)
     {
      s:=2;
     }
     else 
     {  s:=1; }
  }

predicate esteSolutieCorecta(solutie : seq<int>, suma: int)
requires esteSolutieValida(solutie)
{
   solutie[0]*16 + solutie[1]*8 +  solutie[2]*4 + solutie[3]*2 + solutie[4] == suma
}

predicate esteSolutieOptima(solutie : seq<int>, suma: int)
requires esteSolutieValida(solutie)
requires esteSolutieCorecta(solutie, suma)
{
  //nu exista alta solutie cu nr mai mic de bancnote
  forall posibilaSolutie:: esteSolutieValida(posibilaSolutie)&& esteSolutieCorecta(posibilaSolutie,suma)  ==>
  nrBancnoteSol(posibilaSolutie) >= nrBancnoteSol(solutie)
}

predicate esteSolutieValida(solutie : seq<int>)
{
  |solutie| == 5 && solutie[0] >= 0 && solutie[1] >= 0 && solutie[2] >= 0 && solutie[3] >=0 && solutie[4] >=0
}

predicate restCheck(rest : int, suma : int, solutiePrezent : seq<int>)
  requires esteSolutieValida(solutiePrezent)
{
  //vrem sa verificam daca solutia gasita pentru rest+solutia gasita pana in prezent adunate dau solutia finala pentru suma
  //daca gasim o solutie optima pentru rest si solutia pt rest +solutia pana in prezent sunt solutii optime pt suma
  //sol corecta rest si sol(sol rest+sol prezent) corecta suma
   forall solutie ::  esteSolutieValida(solutie) ==>
  (esteSolutieCorecta(solutie, rest) ==> esteSolutieCorecta(sumSolutii(solutie,solutiePrezent), suma) ) 
  &&
  (esteSolutieOptima(solutie, rest) ==> esteSolutieOptima(sumSolutii(solutie,solutiePrezent), suma) )
  
}

//vrem o solutie valida(are formatul specificat) , corecta(creeaza suma data) si optima(creeaza in cel mai eficient mod)
method bancnoteMin(sum: int)returns(sol: seq<int>)
requires sum >=0 
ensures esteSolutieValida(sol)
ensures esteSolutieCorecta(sol, sum)
ensures esteSolutieOptima(sol,sum)
{
   var rest:=sum;
   var s1:=0;
   var s2:=0;
   var s4:=0;
   var s8:=0;
   var s16:=0;
   var s:=0;
   while (0 <rest )
    invariant 0<=rest<=sum
    invariant esteSolutieCorecta( [s16, s8, s4, s2, s1], sum - rest)
    decreases rest
  {
    //la fiecare iteratie se alege bancnota optima
    // pentru a da rest apoi se modifica solutia
    //Every natural number can be written as the sum of Distinct powers of 2.
    //ma pot folosi de asta?
    s:=maximRest(rest);
    if( s ==16)
       { 
        s16:=s16+1;
        assert restCheck(rest-16,sum,[s16, s8, s4, s2, s1]);
        assert esteSolutieCorecta([s16, s8, s4, s2, s1], sum -rest+16); 
        
        //bancnotele date pana acum adunate dau sum-rest curent +16 adaugat acum la bancnotele date
        //ex: mai ai de dat 18 la  din suma totala de 50 , la pasul curent mai dai 16
        //50-18+16=48 aveai s16=2, acum s-a facut s16=3 ,verifici cu predicatul ca 16 16 16 = 48  
       }
       else if( s==8)
       { 
        s8:=s8+1;
        assert restCheck(rest-8,sum,[s16, s8, s4, s2, s1]);
        assert esteSolutieCorecta([s16, s8, s4, s2, s1], sum -rest+8); 
       }
       else if( s==4)
       { 
        s4:=s4+1;
        assert restCheck(rest-4,sum,[s16, s8, s4, s2, s1]);
        assert esteSolutieCorecta([s16, s8, s4, s2, s1], sum -rest+4); 
       }
       else if( s==2)
       { 
        s2:=s2+1;
        assert restCheck(rest-2,sum,[s16, s8, s4, s2, s1]);
        assert esteSolutieCorecta([s16, s8, s4, s2, s1], sum -rest+2); 
       } 
       else 
           { s1:=s1+1;
           assert restCheck(rest-1,sum,[s16, s8, s4, s2, s1]);
           assert esteSolutieCorecta([s16, s8, s4, s2, s1], sum -rest+1); 
           }
 
    rest:=rest-s;//restul de dat 
  }
 
  sol := [s16, s8, s4, s2, s1];
  
}

method Main () 
{
  var sum:=49;
  var bancnote:=new int[5];
  bancnote[0],bancnote[1],bancnote[2],bancnote[3],bancnote[4]:=16,8,4,2,1;
  var n:=5; //dimensiunea secventei bancnote
  var sol := bancnoteMin(sum);
  print "Restul optim pentru suma ";
  print sum;
  print " este: \n";
  print "Numarul bancnote de 16:";
  print sol[0];
  print "\n Nr bancnote de 8:";
  print sol[1];
  print "\n Nr bancnote de 4:";
  print sol[2];
  print "\n Nr bancnote de 2:";
  print sol[3];
  print "\n Nr bancnote de 1:";
  print sol[4];
  
}
