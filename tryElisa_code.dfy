predicate esteSolutieValida(solutie : seq<int>)
{
  |solutie| == 5 && solutie[0] >= 0 && solutie[1] >= 0 && solutie[2] >= 0 && solutie[3] >=0 && solutie[4] >=0
}

predicate esteSolutie(solutie : seq<int>, suma : int)
  requires esteSolutieValida(solutie)
{
    solutie[0] * 1 + solutie[1] * 5 + solutie[2] * 10 + solutie[3] * 20 + solutie[4] * 50 == suma

}


function cost(solutie : seq<int>) : int 
  requires esteSolutieValida(solutie)
{
    solutie[0] + solutie[1] + solutie[2] + solutie[3] + solutie[4]
}

predicate esteSolutieOptima(solutie : seq<int>, suma : int)
    requires esteSolutieValida(solutie)
{   
  esteSolutie(solutie, suma) &&
  forall solutieOarecare :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, suma) 
          ==> cost(solutieOarecare) >= cost(solutie)

}

predicate INV(rest : int, suma : int, solutieFinala : seq<int>)
  requires esteSolutieValida(solutieFinala)
{
   forall solutieCurenta :: esteSolutieValida(solutieCurenta) ==>
          (esteSolutie(solutieCurenta, rest) ==> 
          esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], 
          solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], solutieFinala[4] + solutieCurenta[4]], suma)) &&
          (esteSolutieOptima(solutieCurenta, rest) ==> 
          esteSolutieOptima([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1],
          solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], solutieFinala[4] + solutieCurenta[4]], suma))
}


method gasireMaxim(suma : int) returns(s : int)
  requires suma > 0
  ensures 0 < s <= suma
  ensures s == 1 || s == 5 || s == 10 || s == 20 || s == 50
  ensures s == 1 ==> suma < 5
  ensures s == 5 ==> 5 <= suma < 10
  ensures s == 10 ==> 10 <= suma < 20
  ensures s == 20 ==> 20 <= suma < 50
  ensures s == 50 ==> suma >= 50
{
    if(suma >= 50)
    {
        s := 50 ;
    }
    else if(suma >= 20)
    {
        s := 20;
    }
    else if(suma >= 10)
    {
        s := 10;
    }
    else if(suma >= 5)
    {
        s := 5;
    }
    else if(suma < 5){
        s := 1; 
    }

}


lemma cazMaxim1(rest : int, suma : int, solutieFinala : seq<int>)
  requires rest < 5
  requires esteSolutieValida(solutieFinala)
  requires INV(rest, suma, solutieFinala)
  ensures INV(rest-1, suma, [solutieFinala[0] + 1, solutieFinala[1], solutieFinala[2], solutieFinala[3], solutieFinala[4]])
{

  forall solutieCurenta | esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta, rest - 1) 
          ensures esteSolutieOptima([solutieFinala[0] + solutieCurenta[0] + 1, solutieFinala[1] + solutieCurenta[1],
          solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], solutieFinala[4] + solutieCurenta[4]], suma)
  {
    assert esteSolutie(solutieCurenta, rest - 1);
    assert esteSolutie([solutieCurenta[0] + 1, solutieCurenta[1], solutieCurenta[2], solutieCurenta[3], solutieCurenta[4]], rest);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, rest - 1) 
          ==> cost(solutieOarecare) >= cost(solutieCurenta);

    assert esteSolutie([solutieFinala[0] + solutieCurenta[0] + 1, solutieFinala[1] + solutieCurenta[1],
          solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], solutieFinala[4] + solutieCurenta[4]], suma);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare) &&  esteSolutie(solutieOarecare, suma) 
          ==> cost(solutieOarecare) >= cost([solutieCurenta[0] + solutieFinala[0] + 1, solutieCurenta[1] + solutieFinala[1],
          solutieCurenta[2] + solutieFinala[2], solutieCurenta[3] + solutieFinala[3], solutieCurenta[4] + solutieFinala[4]]);
  }

  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) 
          && esteSolutieOptima(solutieCurenta, rest - 1) ==> 
          esteSolutieOptima([solutieFinala[0] + solutieCurenta[0] + 1, solutieFinala[1] + solutieCurenta[1],
          solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], solutieFinala[4] + solutieCurenta[4]], suma);
}

lemma cazMaxim5(rest : int, suma : int, solutieFinala : seq<int>)
  requires 5 <= rest < 10 
  requires esteSolutieValida(solutieFinala)
  requires INV(rest, suma, solutieFinala)
  ensures INV(rest - 5, suma, [solutieFinala[0], solutieFinala[1] + 1, solutieFinala[2], solutieFinala[3], solutieFinala[4]])
{

 forall solutieCurenta | esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta, rest - 5) 
          ensures esteSolutieOptima([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1] + 1,
          solutieCurenta[2] + solutieFinala[2], solutieCurenta[3] + solutieFinala[3], solutieFinala[4]], suma)
  {
    assert esteSolutie(solutieCurenta, rest - 5);
    assert esteSolutie([solutieCurenta[0], solutieCurenta[1] + 1, solutieCurenta[2], solutieCurenta[3], solutieCurenta[4]], rest);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare)  && esteSolutie(solutieOarecare, rest - 5) 
          ==> cost(solutieOarecare) >= cost(solutieCurenta);
    assert esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1] + 1,
            solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], solutieFinala[4] + solutieCurenta[4]], suma);
    
    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, suma)
          ==> cost(solutieOarecare) >= cost([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1] + 1,
          solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], solutieFinala[4] + solutieCurenta[4]]);
  }

  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) && esteSolutie(solutieCurenta, rest - 5) ==> 
          esteSolutieOptima([solutieCurenta[0] + solutieFinala[0], solutieCurenta[1] + solutieFinala[1] + 1,
          solutieCurenta[2] + solutieFinala[2], solutieCurenta[3] + solutieFinala[3], solutieCurenta[4] + solutieFinala[4]], suma);

}



lemma exchangeArgumentCaz10(rest : int, solutieCurenta : seq<int>)
  requires 10 <= rest < 20
  requires esteSolutieValida(solutieCurenta)
  requires esteSolutieOptima(solutieCurenta, rest - 10)
  ensures esteSolutieOptima([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2] + 1, solutieCurenta[3], solutieCurenta[4]], rest)
{

    assert esteSolutie([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2] + 1, solutieCurenta[3], solutieCurenta[4]], rest);
    if(!esteSolutieOptima([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2] + 1, solutieCurenta[3], solutieCurenta[4]], rest))
    {
      var solutieOptima :|esteSolutieValida(solutieOptima) && esteSolutie(solutieOptima, rest) && 
        cost(solutieOptima) < cost([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2] + 1, solutieCurenta[3], solutieCurenta[4]]);
      assert cost([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2] + 1, solutieCurenta[3], solutieCurenta[4]]) == cost(solutieCurenta) + 1;
      assert solutieOptima[3] == 0;
      assert solutieOptima[4] == 0;
      if(solutieOptima[2] >= 1)
      {
        var solutieOptima' := [solutieOptima[0], solutieOptima[1], solutieOptima[2] - 1, solutieOptima[3], solutieOptima[4]];
        assert esteSolutie(solutieOptima', rest - 10);
        assert cost(solutieOptima') == cost(solutieOptima) - 1;
        assert cost(solutieOptima) - 1 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1] >= 2)
      {
        var solutieOptima' := [solutieOptima[0], solutieOptima[1] - 2, solutieOptima[2], solutieOptima[3], solutieOptima[4]];
        assert esteSolutie(solutieOptima', rest - 10);
        assert cost(solutieOptima') == cost(solutieOptima) - 2;
        assert cost(solutieOptima) - 2 < cost(solutieCurenta);
        assert false;
      }else if(solutieOptima[1] >= 1 && solutieOptima[0] >= 5)
      {
        var solutieOptima' := [solutieOptima[0] - 5, solutieOptima[1] - 1, solutieOptima[2], solutieOptima[3], solutieOptima[4]];
        assert esteSolutie(solutieOptima', rest - 10);
        assert cost(solutieOptima') == cost(solutieOptima) - 6;
        assert cost(solutieOptima) - 6 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[0] >= 10)
      {
        var solutieOptima' := [solutieOptima[0] - 10, solutieOptima[1], solutieOptima[2], solutieOptima[3], solutieOptima[4]];
        assert esteSolutie(solutieOptima', rest - 10);
        assert cost(solutieOptima') == cost(solutieOptima) - 10;
        assert cost(solutieOptima) - 10 < cost(solutieCurenta);
        assert false;
      }
      else{
        assert false;
      }

    }

}



lemma cazMaxim10(rest : int, suma : int, solutieFinala : seq<int>)
  requires 10 <= rest < 20 
  requires esteSolutieValida(solutieFinala) 
  requires INV(rest, suma, solutieFinala)
  ensures INV(rest - 10, suma, [solutieFinala[0], solutieFinala[1], solutieFinala[2] + 1, solutieFinala[3], solutieFinala[4]])
{

 forall solutieCurenta | esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta, rest - 10) 
          ensures esteSolutieOptima([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1],
          solutieCurenta[2] + solutieFinala[2] + 1,solutieCurenta[3] + solutieFinala[3], solutieCurenta[4] + solutieFinala[4]], suma)
  {
    assert esteSolutie(solutieCurenta, rest - 10);
    assert esteSolutie([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2] + 1,solutieCurenta[3], solutieCurenta[4]], rest);

    exchangeArgumentCaz10(rest, solutieCurenta);

    assert esteSolutieOptima([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2] + 1, solutieCurenta[3], solutieCurenta[4]], rest);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, rest - 10) 
          ==> cost(solutieOarecare) >= cost(solutieCurenta);
    

    assert esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], 1 + solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3],solutieFinala[4] + solutieCurenta[4]], suma);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, suma)
          ==> cost(solutieOarecare) >= cost([solutieCurenta[0] + solutieFinala[0], solutieCurenta[1] + solutieFinala[1],
                                        solutieCurenta[2] + solutieFinala[2] + 1,solutieCurenta[3] + solutieFinala[3], solutieCurenta[4] + solutieFinala[4]]);
  }

  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta, rest - 10) ==> 
          esteSolutieOptima([solutieCurenta[0] + solutieFinala[0], solutieCurenta[1] + solutieFinala[1],
                            solutieCurenta[2] + solutieFinala[2] + 1, solutieCurenta[3] + solutieFinala[3], solutieCurenta[4] + solutieFinala[4]], suma);

}



lemma exchangeArgumentCaz20(rest : int, solutieCurenta : seq<int>)
  requires 20 <= rest < 50
  requires esteSolutieValida(solutieCurenta)
  requires esteSolutieOptima(solutieCurenta, rest - 20)
  ensures esteSolutieOptima([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], 1 + solutieCurenta[3], solutieCurenta[4]], rest)
{

    assert esteSolutie([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], 1 + solutieCurenta[3], solutieCurenta[4]], rest);
    if(!esteSolutieOptima([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], 1 + solutieCurenta[3], solutieCurenta[4]], rest))
    {
      var solutieOptima :|esteSolutieValida(solutieOptima) && esteSolutie(solutieOptima, rest) && cost(solutieOptima) < cost([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], 1 + solutieCurenta[3], solutieCurenta[4]]);
      assert cost([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], 1 + solutieCurenta[3], solutieCurenta[4]]) == cost(solutieCurenta) + 1;
      assert solutieOptima[4] == 0;
      if(solutieOptima[3] >= 1)
      {
        var solutieOptima' := [solutieOptima[0], solutieOptima[1], solutieOptima[2], solutieOptima[3] - 1, solutieOptima[4]];
        assert esteSolutie(solutieOptima', rest - 20);
        assert cost(solutieOptima') == cost(solutieOptima) - 1;
        assert cost(solutieOptima) - 1 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2] >= 2)
      {
        var solutieOptima' := [solutieOptima[0], solutieOptima[1], solutieOptima[2] - 2, solutieOptima[3], solutieOptima[4]];
        assert esteSolutie(solutieOptima', rest - 20);
        assert cost(solutieOptima') == cost(solutieOptima) - 2;
        assert cost(solutieOptima) - 2 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2] >= 1 && solutieOptima[1] >= 2)
      {       
        var solutieOptima' := [solutieOptima[0], solutieOptima[1] - 2, solutieOptima[2] - 1, solutieOptima[3], solutieOptima[4]];
        assert esteSolutie(solutieOptima', rest - 20);
        assert cost(solutieOptima') == cost(solutieOptima) - 3;
        assert cost(solutieOptima) - 3 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2] >= 1 && solutieOptima[1] >= 1 && solutieOptima[0] >= 5)
      {
        var solutieOptima' := [solutieOptima[0] - 5, solutieOptima[1] - 1, solutieOptima[2] - 1, solutieOptima[3], solutieOptima[4]];
        assert esteSolutie(solutieOptima', rest - 20);
        assert cost(solutieOptima') == cost(solutieOptima) - 7;
        assert cost(solutieOptima) - 7 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1] >= 4)
      {
        var solutieOptima' := [solutieOptima[0], solutieOptima[1] - 4, solutieOptima[2], solutieOptima[3], solutieOptima[4]];
        assert esteSolutie(solutieOptima', rest - 20);
        assert cost(solutieOptima') == cost(solutieOptima) - 4;
        assert cost(solutieOptima) - 4 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1] >= 3 && solutieOptima[0] >= 5)
      {
        var solutieOptima' := [solutieOptima[0] - 5, solutieOptima[1] - 3, solutieOptima[2], solutieOptima[3], solutieOptima[4]];
        assert esteSolutie(solutieOptima', rest - 20);
        assert cost(solutieOptima') == cost(solutieOptima) - 8;
        assert cost(solutieOptima) - 8 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1] >= 2 && solutieOptima[0] >= 10)
      {
        var solutieOptima' := [solutieOptima[0] - 10, solutieOptima[1] - 2, solutieOptima[2], solutieOptima[3], solutieOptima[4]];
        assert esteSolutie(solutieOptima', rest - 20);
        assert cost(solutieOptima') == cost(solutieOptima) - 12;
        assert cost(solutieOptima) - 12 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1] >= 1 && solutieOptima[0] >= 15)
      {
        var solutieOptima' := [solutieOptima[0] - 15, solutieOptima[1] - 1, solutieOptima[2], solutieOptima[3], solutieOptima[4]];
        assert esteSolutie(solutieOptima', rest - 20);
        assert cost(solutieOptima') == cost(solutieOptima) - 16;
        assert cost(solutieOptima) - 16 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[0] >= 20)
      {
        var solutieOptima' := [solutieOptima[0] - 20, solutieOptima[1], solutieOptima[2], solutieOptima[3], solutieOptima[4]];
        assert esteSolutie(solutieOptima', rest - 20);
        assert cost(solutieOptima') == cost(solutieOptima) - 20;
        assert cost(solutieOptima) - 20 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2] >= 1 && solutieOptima[0] >= 10)
      {
        var solutieOptima' := [solutieOptima[0] - 10, solutieOptima[1], solutieOptima[2] - 1, solutieOptima[3], solutieOptima[4]];
        assert esteSolutie(solutieOptima', rest - 20);
        assert cost(solutieOptima') == cost(solutieOptima) - 11;
        assert cost(solutieOptima) - 11 < cost(solutieCurenta);
        assert false;
      }
      else{
        assert false;
      }
    }
}



lemma cazMaxim20(rest : int, suma : int, solutieFinala : seq<int>)
  requires 20 <= rest < 50 
  requires esteSolutieValida(solutieFinala) 
  requires INV(rest, suma, solutieFinala)
  ensures INV(rest - 20, suma, [solutieFinala[0], solutieFinala[1], solutieFinala[2], solutieFinala[3] + 1, solutieFinala[4]])
{

 forall solutieCurenta | esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta, rest - 20) 
          ensures esteSolutieOptima([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1],
          solutieCurenta[2] + solutieFinala[2], solutieCurenta[3] + solutieFinala[3] + 1, solutieCurenta[4] + solutieFinala[4]], suma)
  {
    assert esteSolutie(solutieCurenta, rest - 20);
    assert esteSolutie([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], solutieCurenta[3] + 1, solutieCurenta[4]], rest);

    exchangeArgumentCaz20(rest, solutieCurenta);

    assert esteSolutieOptima([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], 1 + solutieCurenta[3], solutieCurenta[4]], rest);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, rest - 20) 
          ==> cost(solutieOarecare) >= cost(solutieCurenta);
    

    assert esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], 1 + solutieFinala[3] + solutieCurenta[3], solutieFinala[4] + solutieCurenta[4]], suma);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, suma)
          ==> cost(solutieOarecare) >= cost([solutieCurenta[0] + solutieFinala[0], solutieCurenta[1] + solutieFinala[1],
                                        solutieCurenta[2] + solutieFinala[2], 1 + solutieCurenta[3] + solutieFinala[3], solutieCurenta[4] + solutieFinala[4]]);
  }

  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta, rest - 20) ==> 
          esteSolutieOptima([solutieCurenta[0] + solutieFinala[0], solutieCurenta[1] + solutieFinala[1],
                            solutieCurenta[2] + solutieFinala[2], 1 + solutieCurenta[3] + solutieFinala[3], solutieCurenta[4] + solutieFinala[4]], suma);

}




lemma exchangeArgumentCaz50(rest : int, suma : int, solutieOarecare : seq<int>, solutieCurenta : seq<int>)
  requires esteSolutieValida(solutieOarecare)
  requires esteSolutieValida(solutieCurenta)
  requires rest >= 50
  requires esteSolutie(solutieOarecare, rest)
  requires esteSolutie(solutieCurenta, rest - 50)
  requires esteSolutieOptima(solutieCurenta, rest - 50)
  ensures cost(solutieOarecare) >= cost([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], solutieCurenta[3], 1 + solutieCurenta[4]])
  decreases solutieOarecare[0] + solutieOarecare[1] + solutieOarecare[2] + solutieOarecare[3]
{
  assert esteSolutie(solutieOarecare, rest);
  assert esteSolutie([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], solutieCurenta[3], 1 + solutieCurenta[4]], rest);

  if(cost(solutieOarecare) < cost([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], solutieCurenta[3], 1 + solutieCurenta[4]]))
  {
    if(solutieOarecare[4] > solutieCurenta[4] + 1)
    {
      assert cost([solutieOarecare[0], solutieOarecare[1], solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] - 1]) < cost(solutieCurenta);
      assert esteSolutieOptima([solutieOarecare[0], solutieOarecare[1], solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] - 1], rest - 50);
      assert false;
    }
    else if(solutieOarecare[4] < solutieCurenta[4] + 1)
    {
      assert (solutieOarecare[0] + (5 * solutieOarecare[1])+(10 * solutieOarecare[2]) + (20 * solutieOarecare[3])) >= 50;

      if(solutieOarecare[2] >= 1 && solutieOarecare[3] >= 2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1], solutieOarecare[2] - 1, solutieOarecare[3] - 2, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[2] >= 3 && solutieOarecare[3] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1], solutieOarecare[2] - 3, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[2] >= 5)
      {
          var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1], solutieOarecare[2] - 5, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1] >= 10)
      {
          var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 10, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1] >= 8 && solutieOarecare[2] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 8, solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1] >= 6 && solutieOarecare[2] >= 2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 6, solutieOarecare[2] - 2, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1] >= 6 && solutieOarecare[3] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 6, solutieOarecare[2], solutieOarecare[3] - 1, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1] >= 4 && solutieOarecare[2] >= 3)
      {
          var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 4, solutieOarecare[2] - 3, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1] >= 4 && solutieOarecare[2] >= 1 && solutieOarecare[3] >=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 4, solutieOarecare[2] - 1, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1] >= 2 && solutieOarecare[2] >= 4)
      {
          var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 2, solutieOarecare[2] - 4, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1] >= 2 && solutieOarecare[2] >= 2 && solutieOarecare[3] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 2, solutieOarecare[2] - 2, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1] >= 2 && solutieOarecare[3] >= 2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1] - 2, solutieOarecare[2], solutieOarecare[3] - 2,solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 50)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 50, solutieOarecare[1], solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 45 && solutieOarecare[1] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 45, solutieOarecare[1] - 1, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 40 && solutieOarecare[1] >= 2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 40, solutieOarecare[1] - 2, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 40 && solutieOarecare[2] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 40, solutieOarecare[1], solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 35 && solutieOarecare[1] >= 3)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 35, solutieOarecare[1] - 3, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 35 && solutieOarecare[1] >= 1 && solutieOarecare[2] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 35, solutieOarecare[1] - 1, solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 30 && solutieOarecare[1] >= 4)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 30, solutieOarecare[1] - 4, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 30 && solutieOarecare[1] >= 2 && solutieOarecare[2] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 30, solutieOarecare[1] - 2, solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 30 && solutieOarecare[2] >= 2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 30, solutieOarecare[1], solutieOarecare[2] - 2, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 30 && solutieOarecare[3] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 30, solutieOarecare[1], solutieOarecare[2], solutieOarecare[3] - 1, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 25 && solutieOarecare[1] >= 5)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 25, solutieOarecare[1] - 5, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 25 && solutieOarecare[1] >= 3 &&solutieOarecare[2] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 25, solutieOarecare[1] - 3, solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 25 && solutieOarecare[1] >= 1 &&solutieOarecare[2] >= 2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 25, solutieOarecare[1] - 1, solutieOarecare[2] - 2, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 25 && solutieOarecare[1] >= 1 && solutieOarecare[3] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 25, solutieOarecare[1] - 1, solutieOarecare[2], solutieOarecare[3] - 1, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 20 && solutieOarecare[1] >= 6)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 20, solutieOarecare[1] - 6, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 20 && solutieOarecare[1] >= 4 && solutieOarecare[2] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 20, solutieOarecare[1] - 4, solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 20 && solutieOarecare[1] >= 2 && solutieOarecare[2] >= 2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 20, solutieOarecare[1] - 2, solutieOarecare[2] - 2, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 20 && solutieOarecare[1] >= 2 && solutieOarecare[3] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 20, solutieOarecare[1] - 2, solutieOarecare[2], solutieOarecare[3] - 1, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 20 && solutieOarecare[2] >= 3)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 20, solutieOarecare[1], solutieOarecare[2] - 3, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 20 && solutieOarecare[2] >= 1 && solutieOarecare[3] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 20, solutieOarecare[1], solutieOarecare[2] - 1, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 15 && solutieOarecare[1] >= 7)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 15, solutieOarecare[1] - 7, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 15 && solutieOarecare[1] >= 5 && solutieOarecare[2] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 15, solutieOarecare[1] - 5, solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 15 && solutieOarecare[1] >= 3 && solutieOarecare[2] >= 2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 15, solutieOarecare[1] - 3, solutieOarecare[2] - 2, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 15 && solutieOarecare[1] >= 3 && solutieOarecare[3] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 15, solutieOarecare[1] - 3, solutieOarecare[2], solutieOarecare[3] - 1, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 15 && solutieOarecare[1] >= 1 && solutieOarecare[2] >= 3)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 15, solutieOarecare[1] - 1, solutieOarecare[2] - 3, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 15 && solutieOarecare[1] >= 1 && solutieOarecare[2] >= 1 && solutieOarecare[3] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 15, solutieOarecare[1] - 1, solutieOarecare[2] - 1, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 10 && solutieOarecare[1] >= 8)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1] - 8, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 10 && solutieOarecare[1] >= 6 && solutieOarecare[2] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1] - 6, solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 10 && solutieOarecare[1] >= 4 && solutieOarecare[2] >= 2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1] - 4, solutieOarecare[2] - 2, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 10 && solutieOarecare[1] >= 4 && solutieOarecare[3] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1] - 4, solutieOarecare[2], solutieOarecare[3] - 1, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 10 && solutieOarecare[1] >= 2 && solutieOarecare[2] >= 3)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1] - 2, solutieOarecare[2] - 3, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 10 && solutieOarecare[1] >= 2 && solutieOarecare[2] >= 1 && solutieOarecare[3] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1] - 2, solutieOarecare[2] - 1, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 10 && solutieOarecare[2] >= 4)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1], solutieOarecare[2] - 4, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 10 && solutieOarecare[2] >= 2 && solutieOarecare[3] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1], solutieOarecare[2] - 2, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 10 && solutieOarecare[3] >= 2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1], solutieOarecare[2], solutieOarecare[3] - 2, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 5 && solutieOarecare[1] >= 9)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 9, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 5 && solutieOarecare[1] >= 7 && solutieOarecare[2] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 7, solutieOarecare[2] - 1, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 5 && solutieOarecare[1] >= 5 && solutieOarecare[2] >= 2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 5, solutieOarecare[2] - 2, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 5 && solutieOarecare[1] >= 5 && solutieOarecare[3] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 5, solutieOarecare[2], solutieOarecare[3] - 1, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 5 && solutieOarecare[1] >= 3 && solutieOarecare[2] >= 3)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 3, solutieOarecare[2] - 3, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 5 && solutieOarecare[1] >= 3 && solutieOarecare[2] >= 1 && solutieOarecare[3] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 3, solutieOarecare[2] - 1, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 5 && solutieOarecare[1] >= 1 && solutieOarecare[2] >= 4)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 1, solutieOarecare[2] - 4, solutieOarecare[3], solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 5 && solutieOarecare[1] >= 1 && solutieOarecare[2] >= 2 && solutieOarecare[3] >= 1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 1, solutieOarecare[2] - 2, solutieOarecare[3] - 1, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0] >= 5 && solutieOarecare[1] >= 1 && solutieOarecare[3] >= 2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 1, solutieOarecare[2], solutieOarecare[3] - 2, solutieOarecare[4] + 1];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
      }
      else{
          
          assert solutieOarecare[0] >= 0;
          assert solutieOarecare[1] >= 0;
          assert solutieOarecare[2] >= 0;
          assert solutieOarecare[3] >= 3;
          if(solutieOarecare[3] >= 3)
          {
            var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1], solutieOarecare[2] + 1, solutieOarecare[3] - 3, solutieOarecare[4] + 1];
            assert cost(nouaSolutieOarecare) < cost(solutieOarecare);
            exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
          }
      }
    }

    assert solutieOarecare[4] == (solutieCurenta[4] + 1);


    if(solutieOarecare[3] > solutieCurenta[3])
    {
      assert cost([solutieOarecare[0], solutieOarecare[1], solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] - 1]) < cost(solutieCurenta);
      assert false;
      
    }
    else if(solutieOarecare[3] < solutieCurenta[3])
      {
        assert (solutieOarecare[0] + (5 * solutieOarecare[1]) + (10 * solutieOarecare[2])) > 20;
        
        if(solutieOarecare[2] >= 2)
        {
            assert solutieOarecare[2] >= 2;
            var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1], solutieOarecare[2] - 2, solutieOarecare[3] + 1, solutieOarecare[4]];
            exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[2] >= 1 && solutieOarecare[1] >= 2)
        {
            var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 2, solutieOarecare[2] - 1, solutieOarecare[3] + 1, solutieOarecare[4]];
            exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[2] >= 1 && solutieOarecare[1] >= 1 && solutieOarecare[0] >= 5)
        {
            var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 1, solutieOarecare[2] - 1, solutieOarecare[3] + 1, solutieOarecare[4]];
            exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[1] >= 4)
        {
            var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 4, solutieOarecare[2], solutieOarecare[3] + 1, solutieOarecare[4]];
            exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[1] >= 3 && solutieOarecare[0] >= 5)
        {
            var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 3, solutieOarecare[2], solutieOarecare[3] + 1, solutieOarecare[4]];
            exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[1] >= 2 && solutieOarecare[0] >= 10)
        {
            var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1] - 2, solutieOarecare[2], solutieOarecare[3] + 1, solutieOarecare[4]];
            exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[1] >= 1 && solutieOarecare[0] >= 15)
        {
            var nouaSolutieOarecare := [solutieOarecare[0] - 15, solutieOarecare[1] - 1, solutieOarecare[2], solutieOarecare[3] + 1, solutieOarecare[4]];
            exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[0] >= 20)
        {
            var nouaSolutieOarecare := [solutieOarecare[0] - 20, solutieOarecare[1], solutieOarecare[2], solutieOarecare[3] + 1, solutieOarecare[4]];
            exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[2] >= 1 && solutieOarecare[0] >= 10)
        {
            var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1], solutieOarecare[2] - 1, solutieOarecare[3] + 1, solutieOarecare[4]];
            exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
        }
      }

    assert solutieOarecare[3] == solutieCurenta[3];

    if(solutieOarecare[2] > solutieCurenta[2])
    {
      assert cost([solutieOarecare[0], solutieOarecare[1], solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] - 1]) < cost(solutieCurenta);
      assert false;
    }
    else if(solutieOarecare[2] < solutieCurenta[2])
      {
        assert (solutieOarecare[0] + (5 * solutieOarecare[1])) > 10;

        if(solutieOarecare[0] >= 10)
        {
          var nouaSolutieOarecare := [solutieOarecare[0] - 10, solutieOarecare[1], solutieOarecare[2] + 1, solutieOarecare[3], solutieOarecare[4]];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[1] >= 2){
            var nouaSolutieOarecare := [solutieOarecare[0], solutieOarecare[1] - 2, solutieOarecare[2] + 1, solutieOarecare[3], solutieOarecare[4]];
            exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
        }
          else
          {
            var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] - 1, solutieOarecare[2] + 1, solutieOarecare[3], solutieOarecare[4]];
            exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
          }
        }
        assert solutieOarecare[2] == solutieCurenta[2];

      if(solutieOarecare[1] > solutieCurenta[1])
    {
      assert cost([solutieOarecare[0], solutieOarecare[1], solutieOarecare[2], solutieOarecare[3], solutieOarecare[4] - 1]) < cost(solutieCurenta);
      assert false;
    }
    else
    {
      if(solutieOarecare[1] < solutieCurenta[1])
      {
          assert solutieOarecare[0] >= 5;
          var nouaSolutieOarecare := [solutieOarecare[0] - 5, solutieOarecare[1] + 1, solutieOarecare[2], solutieOarecare[3], solutieOarecare[4]];
          exchangeArgumentCaz50(rest, suma, nouaSolutieOarecare, solutieCurenta);
        
      }
    }
    assert solutieOarecare[0] == solutieCurenta[0];
    assert false;

  }
}

lemma solutieCurentaAreCostMinim(rest : int, suma : int, solutieCurenta : seq<int>)
  requires esteSolutieValida(solutieCurenta)
  requires rest >= 50
  requires esteSolutie(solutieCurenta, rest - 50)
  requires esteSolutieOptima(solutieCurenta, rest - 50)
  ensures esteSolutieOptima([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], solutieCurenta[3], 1 + solutieCurenta[4]], rest)
{
  forall solutieOarecare | esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare, rest)
    ensures cost(solutieOarecare) >= cost([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], solutieCurenta[3], 1 + solutieCurenta[4]])
  {
    exchangeArgumentCaz50(rest, suma, solutieOarecare, solutieCurenta);
  }
  
}


lemma solutieFianalaAreCostMinim(rest : int, suma : int, solutieOarecare : seq<int>, solutieFinala : seq<int>, solutieCurenta : seq<int>)
  requires esteSolutieValida(solutieOarecare)
  requires esteSolutieValida(solutieFinala)
  requires esteSolutieValida(solutieCurenta)
  requires rest >= 50
  requires esteSolutieOptima(solutieCurenta, rest - 50)
  requires esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]], suma)
  requires esteSolutie(solutieOarecare, suma)
  requires INV(rest, suma, solutieFinala)
  ensures cost(solutieOarecare) >= cost([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]])
{
  solutieCurentaAreCostMinim(rest, suma, solutieCurenta);
}




lemma cazMaxim50(rest : int, suma : int, solutieFinala : seq<int>)
  requires rest >= 50
  requires esteSolutieValida(solutieFinala)
  requires INV(rest, suma, solutieFinala)
  ensures INV(rest - 50, suma, [solutieFinala[0], solutieFinala[1], solutieFinala[2], solutieFinala[3], 1 + solutieFinala[4]])
{
  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) ==>
          (esteSolutie(solutieCurenta, rest) ==> 
          esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2],
           solutieFinala[3] + solutieCurenta[3],solutieFinala[4] + solutieCurenta[4]], suma));

   forall solutieCurenta | esteSolutieValida(solutieCurenta) 
          && esteSolutie(solutieCurenta, rest - 50) 
          ensures esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], 
          solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]], suma)
   {
     assert esteSolutie([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], solutieCurenta[3], 1 + solutieCurenta[4]], rest);
   }
  

  forall solutieCurenta | esteSolutieValida(solutieCurenta) 
          && esteSolutieOptima(solutieCurenta, rest - 50) 
          ensures esteSolutieOptima([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2],
           solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]], suma)
  {

    assert esteSolutie(solutieCurenta, rest - 50);
    assert esteSolutie([solutieCurenta[0], solutieCurenta[1], solutieCurenta[2], solutieCurenta[3], 1 + solutieCurenta[4]], rest);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare)
          && esteSolutie(solutieOarecare, rest - 50) 
          ==> cost(solutieOarecare) >= cost(solutieCurenta);


    assert esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], 
      solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]], suma);

    forall solutieOarecare | esteSolutieValida(solutieOarecare)
                 && esteSolutie(solutieOarecare, suma)
      ensures cost(solutieOarecare) >= cost([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]])
      {
          solutieFianalaAreCostMinim(rest, suma, solutieOarecare, solutieFinala, solutieCurenta);
      }

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare)
             && esteSolutie(solutieOarecare, suma) 
          ==> cost(solutieOarecare) >= cost([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]]);
  }


  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta)
          && esteSolutieOptima(solutieCurenta, rest - 50) ==> 
          esteSolutieOptima([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2],
           solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]], suma);


  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) ==>
          (esteSolutie(solutieCurenta, rest - 50) ==> 
          esteSolutie([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2], 
          solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]], suma));
  
  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) ==>        
          (esteSolutieOptima(solutieCurenta, rest - 50) ==> 
          esteSolutieOptima([solutieFinala[0] + solutieCurenta[0], solutieFinala[1] + solutieCurenta[1], solutieFinala[2] + solutieCurenta[2],
           solutieFinala[3] + solutieCurenta[3], 1 + solutieFinala[4] + solutieCurenta[4]], suma));

  assert  INV(rest - 50, suma, [solutieFinala[0], solutieFinala[1], solutieFinala[2], solutieFinala[3], 1 + solutieFinala[4]]);
}



  method nrMinimBancnote(suma : int) returns (solutie : seq<int>)
    requires suma >= 0
    ensures esteSolutieValida(solutie)
    ensures esteSolutie(solutie, suma)
    ensures esteSolutieOptima(solutie, suma)
{

    var rest  :=  suma;
    var s1 := 0;
    var s5 := 0;
    var s10 := 0;
    var s20 := 0;
    var s50 := 0;
    while(rest > 0)
      decreases rest
      invariant 0 <= rest <= suma
      invariant esteSolutie([s1, s5, s10, s20, s50], suma - rest)
      invariant INV(rest, suma, [s1, s5, s10, s20, s50])
    {
        var i := 0;
        var s := gasireMaxim(rest);
        if( s == 1){
            cazMaxim1(rest, suma, [s1, s5, s10, s20, s50]);
            s1 := s1 + 1;
            assert esteSolutie([s1, s5, s10, s20, s50], suma - (rest - 1));
            assert INV(rest - 1, suma, [s1, s5, s10, s20, s50]);
        }
        else if(s == 5)
            {
                cazMaxim5(rest, suma, [s1, s5, s10, s20, s50]);
                s5 := s5 + 1;
                assert esteSolutie([s1, s5, s10, s20, s50], suma - (rest - 5));
                assert INV(rest - 5, suma, [s1, s5, s10, s20, s50]);

            }
            else if (s == 10){
                cazMaxim10(rest, suma, [s1, s5, s10, s20, s50]);
                s10 := s10 + 1;
                assert esteSolutie([s1, s5, s10, s20, s50], suma - (rest - 10));
                assert INV(rest - 10, suma, [s1, s5, s10, s20, s50]);

            }
            else if(s == 20){
                cazMaxim20(rest, suma, [s1, s5, s10, s20, s50]);
                s20 := s20 + 1;
                assert esteSolutie([s1, s5, s10, s20, s50], suma - (rest - 20));
                assert INV(rest - 20, suma, [s1, s5, s10, s20, s50]);
            }
            else{
                cazMaxim50(rest, suma, [s1, s5, s10, s20, s50]);
                s50 := s50 + 1;
                assert esteSolutie([s1, s5, s10, s20, s50], suma - (rest - 50));
                assert INV(rest - 50, suma, [s1, s5, s10, s20, s50]);
            }

        rest := rest - s;
    }
    solutie := [s1, s5, s10, s20, s50];
}


method Main() {
  var suma := 188;
  var solutie := nrMinimBancnote(suma);
  print "Solutia este = ";
  print "1: ";
  print solutie[0];
  print ", ";
  print "5: ";
  print solutie[1];
  print ", ";
  print "10: ";
  print solutie[2];
  print ", ";
  print "20: ";
  print solutie[3];
  print ", ";
  print "50: ";
  print solutie[4];
}