lemma cazMaxim4(rest: int, suma: int, solutieFinala: seq<int>)
  requires 4<=rest < 8
  requires esteSolutieValida(solutieFinala)
  requires INV(rest,suma, solutieFinala)
  ensures INV(rest-4, suma, sumSolutii(solutieFinala, [0,0,1,0,0,0]))

predicate invExcArg(solutieOptima: seq<int>, i: int)
requires i < 5
requires esteSolutieValida(solutieOptima)
{
  0<=i<=4 && solutieOptima[i]<=1 
}


    


lemma exchangeArgumentCaz8(rest: int, solutieCurenta:seq<int>)
    requires 8<=rest < 16
    requires esteSolutieValida(solutieCurenta)
    requires esteSolutieOptima(solutieCurenta, rest-8)
    ensures esteSolutieOptima(sumSolutii(solutieCurenta, [0,0,0,1,0,0]),rest)
  {
      assert esteSolutieCorecta(sumSolutii(solutieCurenta, [0,0,0,1,0,0]),rest);
      if(!esteSolutieOptima(sumSolutii(solutieCurenta, [0,0,0,1,0,0]),rest))
    {
        
      var solutieOptima:| esteSolutieValida(solutieOptima) && esteSolutieCorecta(solutieOptima,rest)&&
          cardinal(solutieOptima) < cardinal(sumSolutii(solutieCurenta, [0,0,0,1,0,0]))&& esteSolutieOptima(solutieOptima,rest);
      assert cardinal(sumSolutii(solutieCurenta, [0,0,0,1,0,0])) == cardinal(solutieCurenta) + 1;
       if(solutieOptima[3] >= 1)
      {
        var solutieOptima' := sumSolutii(solutieOptima, [0,0,0,-1,0,0]);
        assert esteSolutieCorecta(solutieOptima', rest - 8);
        assert cardinal(solutieOptima') == cardinal(solutieOptima) - 1;
        assert cardinal(solutieOptima) - 1 < cardinal(solutieCurenta);
        //adica solutie optima' este optima pt rest-8, iar solutie curenta
        //nu este optima pentru rest-8, required la inceput, contradictie
        assert false;
      }
      else
      { //nu avem 8 in solutie optima
        var i:=3;
        //asiguram ca nu avem mai mult de un 1 , un 2 si un 4 in secventa 
        while ( 0 <= i )
        invariant  -1 <= i <= 3
        invariant invExcArg(solutieOptima,i)
        {
          assert solutieOptima[i]<=1;
          if(solutieOptima[i]>1)
          {
            var s1:=0;
            var s2:=0;
            var s4:=0;
            var s8:=0;
            var s16:=0;
            var s32:=0; 
            if(i==0)
            {
              var s1:=-2;
              var s2:=1;
            }
            else if(i==1)
            {
              var s2:=-2;
              var s4:=1;
            }
              if(i==2)
            {
              var s2:=-2;
              var s4:=1;
            }
            if(i==3)
            {
              var s4:=-2;
              var s8:=1;
            }
            if(solutieOptima[i]>1)
            {
              var solutieOptima' := sumSolutii(solutieOptima, [s1,s2,s4,s8,s16,s32]);
                  //daca avem 2 de i e mai eficient sa avem un i+1.
              assert cardinal(solutieOptima') == cardinal(solutieOptima)-1;
              assert cardinal(solutieOptima') < cardinal(solutieOptima);
              assert cardinal(solutieOptima)-1< cardinal(solutieCurenta);
            }
          }
          i:=i-1;
          
        }
      } 
    }
  }