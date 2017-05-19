resource MiniResBar = open Prelude in {

param
  Gender = Masc | Fem | Neutr ;
  Number = Sg | Pl ;
  Case = Nom | Dat | Acc ;
  Person = P1 | P2 | P3 ;
  Definiteness = Def | Indef ;
  
--  Agreement = Agr Number Person ;

  VForm = Inf | Pres Number Person ;

oper
  Noun : Type = {s : Number => Case => Str ; g : Gender ; massable : Bool } ;

  mkNoun : (sg,pl : Str) -> Gender -> Bool -> Noun = \sg,pl,gen,mass -> {
    s = table { Sg => \\_ => sg ; Pl => \\_ => pl } ;
    g = gen ;
    massable = mass
    } ;

  mkN = overload {
    nkN : Str -> Noun = \sg -> mkNoun sg sg Neutr False;
    nkN : (sg,pl : Str) -> Noun = \sg,pl -> mkNoun sg pl Neutr False;
    nkN : Str -> Gender -> Noun = \sg,gen -> mkNoun sg sg gen False;
    nkN : (sg,pl : Str) -> Gender -> Noun = \sg,pl,gen -> mkNoun sg pl gen False;
    nkN : (sg,pl : Str) -> Gender -> Bool -> Noun = \sg,pl,gen,mass -> mkNoun sg pl gen mass;
    } ;
  
  mkMassN = overload {
    mkMassN : Str ->           Noun = \sg -> mkNoun sg nonExist Neutr True;
    mkMassN : Str -> Gender -> Noun = \sg,g -> mkNoun sg nonExist g True;
    } ;
  
  ProperName : Type = {s : Str ; g : Gender} ;

  mkPN = overload {
    mkPN : Str -> Gender -> ProperName = \pn,gen -> {s = pn ; g = gen} ;
    mkPN : Str -> ProperName = \pn -> {s = pn ; g = Neutr} ;
    } ;

  Adjective : Type = {s : Definiteness => Gender => Number => Case => Str ; base : Str} ;

  mkA : Str -> Adjective = \a -> {
    s =
      let fix : Str * Str * Str = case a of {
	    _ + "a" => <"n","r","a"> ;
	    _ => <"","","">
	    }
      in
      table {
	Def => table {
	  Masc => table {
	    Sg => table { Nom => a + fix.p1 + "e" ; Dat => a + "na" ; Acc => a + "na" } ;
	    Pl => table { _ => a + "n" }
	    } ;
	  Fem => table {
	    Sg => table { Nom => a + fix.p1 + "e" ; Dat => a + "n" + fix.p3 ; Acc => a + fix.p1 + "e" } ;
	    Pl => table { _ => a + "n" }
	    } ;
	  Neutr => table {
	    Sg => table { Nom => a + fix.p1 + "e" ; Dat => a + "na" ; Acc => a + fix.p1 + "e" } ;
	    Pl => table { _ => a + "n" }
	    }
	  } ;
	Indef => table {
	  Masc => table {
	    Sg => table { Nom => a + fix.p2 + "a" ; Dat => a + "n" ; Acc => a + "n" } ;
	    Pl => table { _ => a + fix.p1 + "e" }
	    } ;
	  Fem => table {
	    Sg => table { Nom => a + fix.p1 + "e" ; Dat => a + "n" ; Acc => a + "e" } ;
	    Pl => table { _ => a + fix.p1 + "e" }
	    } ;
	  Neutr => table {
	    Sg => table { Nom => a + fix.p1 + "es" ; Dat => a + "n" ; Acc => a + "e" } ;
	    Pl => table { _ => a + fix.p1 + "e" }
	    }
	  }
      } ;
    base = a      
    } ;
    

  Verb : Type = {s : VForm => Str} ;

  mkVerb : (inf,pressg1,pressg2,pressg3,prespl1,prespl2,prespl3 : Str) -> Verb = \inf,pressg1,pressg2,pressg3,prespl1,prespl2,prespl3 -> {
    s = table {
      Inf => inf ;
      Pres Sg P1 => pressg1 ;
      Pres Sg P2 => pressg2 ;
      Pres Sg P3 => pressg3 ;
      Pres Pl P1 => prespl1 ;
      Pres Pl P2 => prespl2 ;
      Pres Pl P3 => prespl3
      
      }
    } ;

  smartVerb : Str -> Verb = \inf ->
    case inf of {
      i + "a" => mkVerb inf i (i + "st") (i + "t") (inf + "n") (i + "ts") (i + "an") ;
      i + "echn" => mkVerb inf (i + "ech") (i + "ichst") (i + "icht") inf (i + "echts") inf ;
      i + "hn" => mkVerb inf (i + "h") (i + "hst") (i + "ht") inf (i + "hts") inf ;
      i + "n" => mkVerb inf i (i + "st") (i + "t") (i + "an") (i + "ts") inf ;
      i + "m" => mkVerb inf (i + "b") (i + "bst") (i + "bt") inf (i + "bts") inf ;
      _ => mkVerb inf inf (inf + "st") (inf + "t") (inf + "an") (inf + "ts") (inf + "an")
      } ;
 
  mkV = overload {
    mkV : Str -> Verb = smartVerb ;
    mkV : (inf,pressg1,pressg2,pressg3,prespl1,prespl2,prespl3 : Str) -> Verb = mkVerb ;
    } ;

  Verb2 : Type = Verb ** {compl : Str ; c : Case} ;

  mkV2 = overload {
    mkV2 : Str                  -> Verb2 = \s     -> mkV s ** {compl = [] ; c = Acc } ;
    mkV2 : Str  -> Case         -> Verb2 = \s,c   -> mkV s ** {compl = [] ; c = c } ;
    mkV2 : Str  -> Str          -> Verb2 = \s,p   -> mkV s ** {compl = p ; c = Acc } ;
    mkV2 : Verb                 -> Verb2 = \v     -> v     ** {compl = [] ; c = Acc } ;
    mkV2 : Verb -> Case         -> Verb2 = \v,c   -> v     ** {compl = [] ; c = c } ;
    mkV2 : Verb -> Str  -> Case -> Verb2 = \v,p,c -> v     ** {compl = p ; c = c } ;
    mkV2 : Verb -> Str          -> Verb2 = \v,p   -> v     ** {compl = p ; c = Acc } ;
    } ;

  Adverb : Type = {s : Str} ;

  mkAdv : Str -> Adverb = \s -> {s = s} ;

  be_GVerb : GVerb = {
    s = table {
      Inf => "sein" ;
      Pres Sg P1 => "bin" ;
      Pres Sg P2 => "bist" ;
      Pres Sg P3 => "is" ;
      Pres Pl P1 => "san" ;
      Pres Pl P2 => "saids";
      Pres Pl P3 => "san"
       } ;
     isAux = True
     } ;

  GVerb : Type = {
     s : VForm => Str ;
     isAux : Bool
    } ;
  
 oper
   verb2gverb : Verb -> GVerb = \v -> {s = v.s ;
     isAux = False
     } ;

}