concrete MiniGrammarBar of MiniGrammar = open MiniResBar, Prelude in {


  lincat
    Utt = {s : Str} ;
    Adv = Adverb ;
    Pol = {s : Str ; b : Bool} ;
    
    S  = {s : Str} ;
    Cl = {s : Bool => Str} ;
    VP = {verb : GVerb ; compl : Str ; isAP : Bool } ;
    AP = Adjective ;
    CN = {s : Definiteness => Number => Case => Str ; g : Gender ; massable : Bool};
    NP = {s : Case => Str ; g : Gender ; n : Number ; p : Person } ;
    Pron = {s : Case => Str ; g : Gender ; n : Number ; p : Person } ;
    Det = {s : Gender => Case => Str ; n : Number ; d : Definiteness } ;
    Conj = {s : Str} ;
    Prep = {s : Str} ;
    V = Verb ;
    V2 = Verb2 ;
    A = Adjective ;
    N = Noun ;
    PN = ProperName ;

  lin
    UttS s = s ;

    UttNP np = {s = np.s ! Acc} ;

    UsePresCl pol cl = {
      s = pol.s ++ cl.s ! pol.b
      } ;

    PredVP np vp =
      { s = \\b 
	  => np.s ! Nom ++ vp.verb.s ! Pres np.n np.p ++ case <vp.isAP,b> of { <True,True> | <False,_> => "" ; <True,False> => "ned" } ++ vp.compl ++ case <vp.isAP,b> of { <False,True> | <True,_> => "" ; <False,False> => "ned" } ;
      } ;
    
    UseV v = {
      verb = verb2gverb v ;
      compl = [] ;
      isAP = False ;
      } ;
    
    ComplV2 v2 np = {
      verb = verb2gverb v2 ;
      compl = v2.compl ++ np.s ! v2.c ;
      isAP = False
      } ;
    
    UseAP ap = {
      verb = be_GVerb ;
      compl = ap.base ;
      isAP = True
      } ;
    
    AdvVP vp adv =
      vp ** {compl = adv.s ++ vp.compl} ;
      
    DetCN det cn = {
      s = \\c => det.s ! cn.g ! c ++ cn.s ! det.d ! det.n ! c;
      g = cn.g ;
      n = det.n ;
      p = P3
      } ;
    
    UsePN pn = {
       s = \\c => case pn.g of { Fem | Masc => the_Det.s ! pn.g ! c ; Neutr => "" } ++ pn.s ;
       g = pn.g ;
       n = Sg ;
       p = P3
       } ;

    UsePron p =
      p ;
    
    MassNP cn =
      {
	s = \\c => case cn.massable of { True => cn.s ! Indef ! Sg ! c ;  False => nonExist };
	g = cn.g ;
	n = Sg ;
	p = P3
	} ;
    
    a_Det = {
      s = \\g,c => case <g,c> of {
	<_,Nom> => "a" ;
	<Masc|Neutr,Dat> => "an" ;
	<Fem,Dat> => "ara" ;
	<Masc,Acc> => "an" ;
	<Fem|Neutr,Acc> => "a"		
	};
      n = Sg ;
      d = Indef 
      } ;

    aPl_Det = {
      s = \\_,_ => "" ;
      n = Pl ;
      d = Indef
      } ;

    the_Det = {
      s = table {
	Masc => table { Nom => "da"; Dat => "am" ; Acc => "an" } ;
	Fem => table { Nom => "d" ; Dat => "da" ; Acc => "d" } ;
	Neutr => table { Nom => "as" ; Dat => "am" ; Acc => "as" }
	} ;
      n = Sg ;
      d = Def
      } ;

    thePl_Det = {
      s = \\_ => table { Nom => "d" ; Dat => "de" ; Acc => "d" } ;
      n = Pl ;
      d = Def 
      } ;

    UseN n =
      { s = \\_ => n.s ; g = n.g ; massable = n.massable } ;

    AdjCN ap cn = {
      s = \\d,n,c => ap.s ! d ! cn.g ! n ! c ++ cn.s ! d ! n ! c ;
      g = cn.g ;
      massable = cn.massable
      } ;

    PositA a = a ;

    PrepNP prep np = {s = prep.s ++ np.s ! Acc} ;

    CoordS conj a b = {s = a.s ++ conj.s ++ b.s} ;
    
    PPos  = {s = [] ; b = True} ;
    PNeg  = {s = [] ; b = False} ;

    and_Conj = {s = "und"} ;

    or_Conj = {s = "oda"} ;

    every_Det = {
      s = table {
	Masc => table { Nom => "jeda" ; Dat => "jem" ; Acc => "jedn" } ;
	Fem => table { Nom => "jede" ;  Dat => "jeda" ; Acc => "jede" } ;
	Neutr => table { Nom => "jeds" ; Dat => "jem" ; Acc => "jeds" }
	};
      n = Sg ;
      d = Def ;
      } ;

    in_Prep = {s = "i"} ;

    on_Prep = {s = "aufm"} ;

    with_Prep = {s = "mid"} ;

    i_Pron = {
      s = table {Nom => "i" ; Dat => "mia" ; Acc => "mi" } ;
      gen = "meina" ;
      g = Fem | Masc ;
      n = Sg ;
      p = P1
      } ;
    
    youSg_Pron = {
      s = table {Nom => "du" ; Dat => "dia" ; Acc => "di" } ;
      gen = "deina" ;
      g = Fem | Masc ;
      n = Sg ;
      p = P2 
      } ;
    
    he_Pron = {
      s = table {Nom => "ea" ; Dat => "eahm" ; Acc => "eahm" } ;
      gen = "seina" ;
      g = Masc ;
      n = Sg ;
      p = P3 
      } ;
    
    she_Pron = {
      s = table {Nom => "sie" ; Dat => "iara" ; Acc => "sie" } ;
      gen = "iara" ;
      g = Fem ;
      n = Sg ;
      p = P3 
      } ;
    
    we_Pron = {
      s = table {Nom => "mia" ; Dat => "uns" ; Acc => "uns"} ;
      gen = "unsa" ; 
      g = Fem | Masc ;
      n = Pl ;
      p = P1 
      } ;
    
    youPl_Pron = {
      s = table {Nom => "ia" ; Dat => "eich" ; Acc => "eich"} ;
      gen = "eia" ; 
      g = Fem | Masc ;
      n = Pl ;
      p = P2
      } ;
    
    they_Pron = {
      s = table {Nom => "de" ; Dat => "eahna" ; Acc => "de"} ;
      gen = "eahna" ;
      g = Fem | Masc ;
      n = Pl ;
      p = P3 
      } ;

}
