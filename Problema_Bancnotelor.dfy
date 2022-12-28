predicate esteSolutieValida(solutie : seq<int>)
{
  |solutie| == 5 && solutie[0] >= 0 && solutie[1] >= 0 && solutie[2] >= 0 && solutie[3] >=0 && solutie[4] >=0
}

predicate are5elem(solutie : seq<int>)
{
  |solutie| == 5
}

function sumSolutii(s1 : seq<int>,s2 : seq<int>): seq<int>
requires are5elem(s1)
requires are5elem(s2)
{
  [s1[0]+s2[0], s1[1]+s2[1], s1[2]+s2[2], s1[3]+s2[3],s1[4]+s2[4]]
}

predicate esteSolutieCorecta(solutie : seq<int>, suma: int)
requires esteSolutieValida(solutie)
{
   solutie[0]*1 + solutie[1]*2 +  solutie[2]*4 + solutie[3]*8 + solutie[4]*16 == suma
}

function cardinal(solutie : seq<int>): int
requires esteSolutieValida(solutie)
{
  solutie[0] + solutie[1] +  solutie[2] + solutie[3] + solutie[4]
}

predicate esteSolutieOptima(solutie : seq<int>, suma: int)
requires esteSolutieValida(solutie)
{
  //nu exista alta solutie cu nr mai mic de bancnote
  esteSolutieCorecta(solutie, suma)&&
  forall posibilaSolutie:: esteSolutieValida(posibilaSolutie)&& esteSolutieCorecta(posibilaSolutie,suma)  ==>
  cardinal(posibilaSolutie) >= cardinal(solutie)
}

predicate INV(rest : int, suma : int, solutiePrezent : seq<int>)
  requires esteSolutieValida(solutiePrezent)
{

  forall solutie :: esteSolutieValida(solutie)==>
        (esteSolutieCorecta(solutie,rest) ==>
        esteSolutieCorecta(sumSolutii(solutie,solutiePrezent) ,suma) )
        &&
        ( esteSolutieOptima(solutiePrezent,rest)==>
          esteSolutieOptima(sumSolutii(solutie,solutiePrezent),suma) )
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
     else if(suma<2) 
     {  s:=1; }
  }


lemma cazMaxim1(rest: int, suma: int, solutieFinala: seq<int>)
  requires  rest == 1
  requires esteSolutieValida(solutieFinala)
  requires INV(rest,suma, solutieFinala)
  ensures INV(rest-1, suma, sumSolutii(solutieFinala, [1,0,0,0,0]))

lemma cazMaxim2(rest: int, suma: int, solutieFinala: seq<int>)
  requires 2<=rest < 4
  requires esteSolutieValida(solutieFinala)
  requires INV(rest,suma, solutieFinala)
  ensures INV(rest-2, suma, sumSolutii(solutieFinala, [0,1,0,0,0]))
 

lemma cazMaxim4(rest: int, suma: int, solutieFinala: seq<int>)
  requires 4<=rest < 8
  requires esteSolutieValida(solutieFinala)
  requires INV(rest,suma, solutieFinala)
  ensures INV(rest-4, suma, sumSolutii(solutieFinala, [0,0,1,0,0]))

lemma exchangeArgumentCaz8(rest: int, solutieCurenta:seq<int>)
    requires 8<=rest < 16
    requires esteSolutieValida(solutieCurenta)
    requires esteSolutieOptima(solutieCurenta, rest-8)
    ensures esteSolutieOptima(sumSolutii(solutieCurenta, [0,0,0,1,0]),rest)
    {

      assert esteSolutieCorecta(sumSolutii(solutieCurenta, [0,0,0,1,0]),rest);
        if(!esteSolutieOptima(sumSolutii(solutieCurenta, [0,0,0,1,0]),rest))
      {
        var solutieOptima:| esteSolutieValida(solutieOptima) && esteSolutieCorecta(solutieOptima,rest)&&
          cardinal(solutieOptima) < cardinal(sumSolutii(solutieCurenta, [0,1,0,0,0]));

      assert cardinal(sumSolutii(solutieCurenta, [0,0,0,1,0])) == cardinal(solutieCurenta) + 1;
      assert solutieOptima[4] == 0;
      if(solutieOptima[3] >= 1)
      {
        var solutieOptima' := sumSolutii(solutieOptima, [0,0,0,-1,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 8);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 1;
        assert cardinal(solutieOptima) - 1 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2] >= 2)
      {
        var solutieOptima' :=sumSolutii(solutieOptima,[0,0,-2,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 8);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 2;
        assert cardinal(solutieOptima) - 2 < cardinal(solutieCurenta);
        assert false;
      }else if(solutieOptima[2] >= 1 && solutieOptima[1] >= 2)
      {
        var solutieOptima' := sumSolutii(solutieOptima,[0,-2,-1,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 8);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 3;
        assert cardinal(solutieOptima) - 3 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1] >= 4)
      {
        var solutieOptima' := sumSolutii(solutieOptima,[0,-4,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 8);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 4;
        assert cardinal(solutieOptima) - 4 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2] >= 1 &&solutieOptima[1]>=1 && solutieOptima[0]>=2)
      {
        var solutieOptima' := sumSolutii(solutieOptima,[-2,-1,-1,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 8);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 4;
        assert cardinal(solutieOptima) - 4 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2] >= 1 && solutieOptima[0]>=4)
      {
        var solutieOptima' := sumSolutii(solutieOptima,[-4,0,-1,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 8);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 5;
        assert cardinal(solutieOptima) - 5 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1] >= 3 && solutieOptima[0]>=2)
      {
        var solutieOptima' := sumSolutii(solutieOptima,[-2,-3,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 8);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 5;
        assert cardinal(solutieOptima) - 5 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1] >= 2 && solutieOptima[0]>=4)
      { //2 2 1 1 1 1 = 8
        var solutieOptima' := sumSolutii(solutieOptima,[-4,-2,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 8);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 6;
        assert cardinal(solutieOptima) - 6 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1] >= 1 &&solutieOptima[0]>=6 )
      {
        var solutieOptima' := sumSolutii(solutieOptima,[-6,-1,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 8);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 7;
        assert cardinal(solutieOptima) - 7 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[0]>=8)
      {
        var solutieOptima' := sumSolutii(solutieOptima,[-8,0,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 8);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 8;
        assert cardinal(solutieOptima) - 8 < cardinal(solutieCurenta);
        assert false;
      }
      else{
        assert false;
      }

    }

}

lemma cazMaxim8(rest: int, suma: int, solutieFinala: seq<int>)
  requires 8<=rest < 16
  requires esteSolutieValida(solutieFinala)
  requires INV(rest,suma, solutieFinala)
  ensures INV(rest-8, suma, sumSolutii(solutieFinala, [0,0,0,1,0]))
  {

    forall solutieCurenta | esteSolutieValida(solutieCurenta)&& esteSolutieOptima(solutieCurenta,rest-8)
       ensures esteSolutieOptima(sumSolutii(solutieCurenta,sumSolutii(solutieFinala, [0,1,0,0,0])), suma)
            {

            assert esteSolutieCorecta(solutieCurenta, rest - 8);
            assert esteSolutieCorecta(sumSolutii(solutieCurenta, [0,0,0,1,0]),rest);
            exchangeArgumentCaz8(rest, solutieCurenta);
 
            }

    assert forall solutieCurenta:: esteSolutieValida(solutieCurenta)&& esteSolutieOptima(solutieCurenta,rest-8)
        ==> esteSolutieOptima(sumSolutii(solutieCurenta,sumSolutii(solutieFinala,[0,1,0,0,0])),suma);

  }

lemma exchangeArgumentCaz16(rest: int, solutieCurenta:seq<int>)
    requires 16<=rest 
    requires esteSolutieValida(solutieCurenta)
    requires esteSolutieOptima(solutieCurenta, rest-16)
    ensures esteSolutieOptima(sumSolutii(solutieCurenta, [1,0,0,0,0]),rest)
    {
      assert esteSolutieCorecta(sumSolutii(solutieCurenta, [1,0,0,0,0]),rest);
        if(!esteSolutieOptima(sumSolutii(solutieCurenta, [1,0,0,0,0]),rest))
      {
        var solutieOptima:| esteSolutieValida(solutieOptima) && esteSolutieCorecta(solutieOptima,rest)&&
          cardinal(solutieOptima) < cardinal(sumSolutii(solutieCurenta,[1,0,0,0,0]));

      assert cardinal(sumSolutii(solutieCurenta, [1,0,0,0,0])) == cardinal(solutieCurenta) + 1;
      /*if(solutieOptima[1] >= 1)
      {
        var solutieOptima' := sumSolutii(solutieOptima, [0,-1,0,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 8);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 1;
        assert cardinal(solutieOptima) - 1 < cardinal(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2] >= 2)
      {
        var solutieOptima' :=sumSolutii(solutieOptima,[0,0,-2,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 8);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 2;
        assert cardinal(solutieOptima) - 2 < cardinal(solutieCurenta);
        assert false;
      }
      else{
        assert false;
      }
      */

    }

}


lemma cazMaxim16(rest: int, suma: int, solutieFinala: seq<int>)
requires 16<=rest 
  requires esteSolutieValida(solutieFinala)
  requires INV(rest,suma, solutieFinala)
  ensures INV(rest-16, suma, sumSolutii(solutieFinala, [1,0,0,0,0]))
  {

    forall solutieCurenta | esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta,rest-16)
          ensures esteSolutieOptima(sumSolutii(sumSolutii(solutieCurenta,solutieFinala),[1,0,0,0,0]),suma)
    {

      assert esteSolutieCorecta(solutieCurenta,rest-16);
      assert esteSolutieCorecta(sumSolutii(solutieCurenta,[1,0,0,0,0]),rest);

      exchangeArgumentCaz16(rest, solutieCurenta);

      assert forall solutie ::esteSolutieValida(solutie)&& esteSolutieCorecta(solutie, rest-16)
        ==>cardinal(solutie) >= cardinal(solutieCurenta);

        assert esteSolutieCorecta(sumSolutii(sumSolutii(solutieCurenta,solutieFinala),[1,0,0,0,0]),suma);


        assert forall solutie :: esteSolutieValida(solutie)&&esteSolutieCorecta(solutie,suma)
          ==> cardinal(solutie)>= cardinal(sumSolutii(sumSolutii(solutieCurenta,solutieFinala),[1,0,0,0,0]));
    
    }

    assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta,rest-16)
           ==> esteSolutieOptima(sumSolutii(sumSolutii(solutieCurenta,solutieFinala),[1,0,0,0,0]),suma);
  
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
    invariant esteSolutieCorecta( [s1, s2, s4, s8, s16], sum - rest)
    invariant INV(rest,sum,[s1, s2, s4, s8, s16])
    decreases rest
  {
    //la fiecare iteratie se alege bancnota optima
    // pentru a da rest apoi se modifica solutia
    
    s:=maximRest(rest);
     if( s==1){ 
            cazMaxim1(rest,sum,[s1, s2, s4, s8, s16]);
            s1:=s1+1;
           assert esteSolutieCorecta([s1, s2, s4, s8, s16], sum -rest+1); 
           assert INV(rest-1,sum,[s1, s2, s4, s8, s16]);
           } 
      else if( s==2)
       { 
        cazMaxim2(rest,sum,[s1, s2, s4, s8, s16]);
        s2:=s2+1;
        assert esteSolutieCorecta([s1, s2, s4, s8, s16], sum -rest+2); 
        assert INV(rest-2,sum,[s1, s2, s4, s8, s16]);
       } 
       else  if( s==4)
       { 
        cazMaxim4(rest,sum,[s1, s2, s4, s8, s16]);
        s4:=s4+1;
        assert esteSolutieCorecta([s1, s2, s4, s8, s16], sum -rest+4); 
        assert INV(rest-4,sum,[s1, s2, s4, s8, s16]);
       }
       else if( s==8)
       { 
        cazMaxim8(rest,sum,[s1, s2, s4, s8, s16]);
        s8:=s8+1;
        assert esteSolutieCorecta([s1, s2, s4, s8, s16], sum -rest+8); 
        assert INV(rest-8,sum,[s1, s2, s4, s8, s16]);
       }
       else if( s ==16)
       { 
        cazMaxim16(rest,sum,[s1, s2, s4, s8, s16]);
        s16:=s16+1;
        assert esteSolutieCorecta([s1, s2, s4, s8, s16], sum -rest+16); 
        assert INV(rest-16,sum,[s1, s2, s4, s8, s16]);
       }
       
    rest:=rest-s;//restul de dat 
  }
 
  sol := [s1, s2, s4, s8, s16];
  //s1, s2, s4, s8, s16
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
  print "Numarul bancnote de 1:";
  print sol[0];
  print "\n Nr bancnote de 2:";
  print sol[1];
  print "\n Nr bancnote de 4:";
  print sol[2];
  print "\n Nr bancnote de 8:";
  print sol[3];
  print "\n Nr bancnote de 16:";
  print sol[4];
  
}
