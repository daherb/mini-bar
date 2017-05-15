resource MiniResBar = open Prelude in {

param
  Number = Sg | Pl ;
  Case = Nom | Acc ;
  Person = Per1 | Per2 | Per3 ;

  Agreement = Agr Number Person ;

  VForm = Inf | PresSg Person | PresPl Person ;

oper
  Noun : Type = {s : Str} ;

  mkNoun : Str -> Noun = \sg -> {
    s = sg
    } ;

  mkN : Str -> Noun = mkNoun ;

  ProperName : Type = {s : Str} ;

  mkPN : Str -> ProperName = \s -> {s = s} ;

  Adjective : Type = {s : Str} ;

  mkA : Str -> Adjective = \s -> {s = s} ;

  Verb : Type = {s : VForm => Str} ;

  mkVerb : (inf,pressg1,pressg2,pressg3,prespl1,prespl2,prespl3 : Str) -> Verb = \inf,pressg1,pressg2,pressg3,prespl1,prespl2,prespl3 -> {
    s = table {
      Inf => inf ;
      PresSg P1 => pressg1 ;
      PresSg P2 => pressg2 ;
      PresSg P3 => pressg3 ;
      PresPl P1 => prespl1 ;
      PresPl P2 => prespl2 ;
      PresPl P3 => prespl3
      
      }
    } ;

  smartVerb : Str -> Verb = \inf ->
    case inf of {
      i + "a" => mkVerb inf i (i + "st") (i + "t") inf (i + "t") (i + "an") ;
      i + "n" => mkVerb inf i (i + "st") (i + "t") (i + "an") (i + "ts") inf
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
      PresSg P1 => "bin" ;
      PresSg P2 => "bist" ;
      PresSg P3 => "is" ;
      PresPl P1 => "san" ;
      PresPl P2 => "saids";
      PresPl P3 => "san"
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