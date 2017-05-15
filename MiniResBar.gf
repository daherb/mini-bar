resource MiniResBar = open Prelude in {

param
  Gender = Masc | Fem | Neutr ;
  Number = Sg | Pl ;
  Case = Nom | Dat | Acc ;
  Person = P1 | P2 | P3 ;

--  Agreement = Agr Number Person ;

  VForm = Inf | Pres Number Person ;

oper
  Noun : Type = {s : Number => Case => Str ; g : Gender} ;

  mkNoun : (sg,pl : Str) -> Gender -> Noun = \sg,pl,gen -> {
    s = table { Sg => \\_ => sg ; Pl => \\_ => pl } ;
    g = gen
    } ;

  mkN = overload {
    nkN : Str -> Noun = \sg -> mkNoun sg sg Neutr ;
    nkN : (sg,pl : Str) -> Noun = \sg,pl -> mkNoun sg pl Neutr ;
    nkN : Str -> Gender -> Noun = \sg,gen -> mkNoun sg sg gen ;
    nkN : (sg,pl : Str) -> Gender -> Noun = mkNoun ;
    } ;

  ProperName : Type = {s : Str ; g : Gender} ;

  mkPN = overload {
    mkPN : Str -> Gender -> ProperName = \pn,gen -> {s = pn ; g = gen} ;
    mkPN : Str -> ProperName = \pn -> {s = pn ; g = Neutr} ;
    } ;

  Adjective : Type = {s : Gender => Number => Case => Str ; base : Str} ;

  mkA : Str -> Adjective = \a -> {
    s = table { Masc => table {
		  Sg => table { Nom => a + "e" ; Dat => a + "n" ; Acc => a + "n" } ;
		  Pl => table { _ => a + "n" }
		  } ;
		Fem => table {
		  Sg => table { Nom => a + "e" ; Dat => a + "n" ; Acc => a + "e" } ;
		  Pl => table { _ => a + "n" }
		  } ;
		Neutr => table {
		  Sg => table { Nom => a + "e" ; Dat => a + "n" ; Acc => a + "e" } ;
		  Pl => table { _ => a + "n" }
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
      i + "a" => mkVerb inf i (i + "st") (i + "t") inf (i + "t") (i + "an") ;
      i + "n" => mkVerb inf i (i + "st") (i + "t") (i + "an") (i + "ts") inf ;
      i + "m" => mkVerb inf i (i + "bst") (i + "bt") inf (i + "bts") inf ;
      _ => mkVerb inf inf (inf + "st") (inf + "t") (inf + "an") (inf + "ts") inf
      } ;
 
  mkV = overload {
    mkV : Str -> Verb = smartVerb ;
    mkV : (inf,pressg1,pressg2,pressg3,prespl1,prespl2,prespl3 : Str) -> Verb = mkVerb ;
    } ;

  Verb2 : Type = Verb ** {c : Str} ;

  mkV2 = overload {
    mkV2 : Str         -> Verb2 = \s   -> mkV s ** {c = []} ;
    mkV2 : Str  -> Str -> Verb2 = \s,p -> mkV s ** {c = p} ;
    mkV2 : Verb        -> Verb2 = \v   -> v ** {c = []} ;
    mkV2 : Verb -> Str -> Verb2 = \v,p -> v ** {c = p} ;
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