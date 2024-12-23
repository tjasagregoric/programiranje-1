(* # 1. domača naloga *)

(* ## Ogrevanje *)

(** Števke *)

let rec stevke n b = 
   if b < n then [b] else (
      stevke n (b / n)  @ [b mod n]
   )

(* let primer_1_1 = stevke 10 12345 *)
(* let primer_1_2 = stevke 2 42 *)
(* let primer_1_3 = stevke 16 ((3 * 16 * 16 * 16) + (14 * 16 * 16) + (15 * 16) + 9) *)

(** Začetek seznama *)

let rec take st sez = 
   match (sez, st) with
   | ([], _) -> []
   | (_, 0) -> []
   | (x :: xs, _) -> x :: take (st-1) xs

(* let primer_1_4 = take 3 [ 1; 2; 3; 4; 5 ] *)
(* let primer_1_5 = take 10 [ 1; 2; 3; 4; 5 ] *)

(** Odstranjevanje ujemajočih *)

let rec drop_while predikat sez =
   match sez with
   | x :: xs when predikat x -> drop_while predikat xs
   | _ -> sez

(* let primer_1_6 = drop_while (fun x -> x < 5) [ 3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5 ] *)
(* let primer_1_7 = drop_while (fun x -> x < 5) [ 9; 8; 7; 6; 5; 4; 3; 2; 1; 0 ] *)

(** Funkcija `filter_mapi` *)

let filter_mapi f sez = 
   let rec filter_mapi_rep i sez=
   match sez with
   | [] -> []
   | x :: xs -> 
      match f i x with
      | Some rezultat -> rezultat :: filter_mapi_rep (i +1) xs
      | None -> filter_mapi_rep (i +1) xs
   in
   filter_mapi_rep 0 sez

(* let primer_1_8 =
   filter_mapi
     (fun i x -> if i mod 2 = 0 then Some (x * x) else None)
     [ 1; 2; 3; 4; 5; 6; 7; 8; 9 ] *)

(* ## Izomorfizmi množic *)

type ('a, 'b) sum = In1 of 'a | In2 of 'b

(** $A \times B \cong B \times A$ *)

let phi1 (a, b) = (b, a)
let psi1 (b, a) = (a, b)

(** $A + B \cong B + A$ *)

let phi2 = 
   function
   |In1 a -> In2 a
   |In2 b -> In1 b

let psi2  = 
   function
   |In1 b -> In2 b
   |In2 a -> In1 a

(** $A \times (B \times C) \cong (A \times B) \times C$ *)

let phi3 (a, (b,c)) = ((a,b), c)
let psi3 ((a,b), c) = (a, (b,c))

(** $A + (B + C) \cong (A + B) + C$ *)

let phi4  = 
   function
   | In1 a -> In1 (In1 a)
   | In2 (In1 b) -> In1 (In2 b)
   | In2 (In2 c) -> In2 c

let psi4  = 
   function
   | In1 (In1 a) -> In1 a
   | In1 (In2 b) -> In2 (In1 b)
   | In2 c -> In2 (In2 c)

(** $A \times (B + C) \cong (A \times B) + (A \times C)$ *)

let phi5  = 
   function
   | (a, In1 b) -> In1 (a, b)
   | (a, In2 c) -> In2 (a, c)

let psi5  = 
   function
   | In1 (a, b) -> (a, In1 b) 
   | In2 (a, c) -> (a, In2 c)

(** $A^{B + C} \cong A^B \times A^C$ *)

let phi6 f = 
   let g = (fun b -> f (In1 b)) in
   let h = (fun c -> f (In2 c)) in
   (g, h)

let psi6 (f, g)= 
   function
   | In1 b -> f b
   | In2 c -> g c

(** $(A \times B)^C \cong A^C \times B^C$ *)

let phi7 f = 
   let g  = fun c -> fst (f c) in 
   let h = fun c -> snd(f c) in 
   (g, h)

let psi7 (g, h) = fun c -> (g c, h c)

(* ## Polinomi *)

type polinom = int list

(** Odstranjevanje odvečnih ničel *)
let rec pomozna sez=
   match sez with
   | x :: xs when x = 0 -> pomozna xs
   | _ -> sez

let pocisti polinom = 
   let obrnjen = List.rev polinom in
   List.rev (pomozna obrnjen)
   
(* let primer_3_1 = pocisti [ 1; -2; 3; 0; 0 ] *)

(** Seštevanje *)
let rec dodaj_nicle pol1 n =
    match n with
    | 0 -> pol1
    | _ -> dodaj_nicle pol1 (n-1) @ [0]

let rec ( +++ ) pol1 pol2 =

   let len1 = List.length pol1 in
   let len2 = List.length pol2 in
   if len1 >= len2 then 
      let pol = dodaj_nicle pol2 (len1 - len2) in
         pocisti(List.map2 (+) pol1 pol)
else (+++) pol2 pol1

(* let primer_3_2 = [ 1; -2; 3 ] +++ [ 1; 2 ] *)
(* let primer_3_3 = [ 1; -2; 3 ] +++ [ 1; 2; -3 ] *)

(** Množenje *)
let loci_zadnji sez =
   match List.rev sez with
   | [] -> failwith "seznam je prazen"
   | x :: xs -> (List.rev xs , xs)

let ( *** ) pol1 pol2 = 
let rec mnozenje_rep pol1 pol2 acc =
   match pol2 with
   | [] -> acc
   | x :: xs -> 
      let(konec, sez_pomozni) = loci_zadnji (List.map (fun y -> x*y) pol1) in
      match acc with
      |[] -> mnozenje_rep pol1 xs (sez_pomozni @ konec)
      |l :: ls -> mnozenje_rep pol1 xs (l :: ((List.map2 (+) sez_pomozni ls) @ konec))
   in
   mnozenje_rep pol1 pol2 []

(* let primer_3_4 = [ 1; 1 ] *** [ 1; 1 ] *** [ 1; 1 ] *)
(* let primer_3_5 = [ 1; 1 ] *** [ 1; -1 ] *)

(** Izračun vrednosti v točki *)
let rec pow x y =
   if y = 0 then 1 else x * pow x (y-1)

let vrednost pol vr = 
   let rec vrednost_rep pol vr acc s=
      match pol with
      |[] -> acc
      | x :: xs -> vrednost_rep xs vr (acc +( x * pow vr s)) (s +1) 
   in
   vrednost_rep pol vr 0 0

(* let primer_3_6 = vrednost [ 1; -2; 3 ] 2 *)

(** Odvajanje *)
let odvzem_prvega_el sez=
   match sez with
   | [] -> []
   | x :: xs -> xs

let odvod pol = 
   let rec odvod_rep pol s acc =
      match pol with
      |[] -> acc
      | x :: xs -> odvod_rep xs (s +1) (acc @ [x*s])
   in
   odvod_rep (odvzem_prvega_el pol) 1 []

(* let primer_3_7 = odvod [ 1; -2; 3 ] *)

(** Lep izpis *)

let izpis pol =
   let rec izpis_rep pol eksp niz =
     match pol with
     | [] -> niz
     | 0 :: xs -> izpis_rep xs (eksp - 1) niz  
     | x :: xs ->
       let clen =
         match eksp with
         | 0 -> string_of_int (abs x)
         | 1 -> (if (abs x) = 1 then "" else string_of_int (abs x)) ^ " x"
         | _ -> (if (abs x) = 1 then "" else string_of_int (abs x)) ^ " x^" ^ string_of_int eksp
       in
       let znak = if x > 0 && niz <> "" then " + " else if x < 0 then " -" else "" 
       in
       izpis_rep xs (eksp - 1) (niz ^ znak ^ clen)
   in
   izpis_rep (List.rev pol) (List.length pol - 1) ""
 

(* let primer_3_8 = izpis [ 1; 2; 1 ] *)
(* let primer_3_9 = izpis [ 1; 0; -1; 0; 1; 0; -1; 0; 1; 0; -1; 0; 1 ] *)
(* let primer_3_10 = izpis [ 0; -3; 3; -1 ] *)

(* ## Samodejno odvajanje *)

let priblizek_odvoda f x0 h = (f (x0 +. h) -. f x0) /. h

(* let primer_3_11 =
   let f x = sin x +. cos x +. exp x in
   List.map (priblizek_odvoda f 1.) [ 0.1; 0.01; 0.001; 0.0001; 0.00001 ] *)

type odvedljiva = (float -> float) * (float -> float)

let sinus : odvedljiva = (sin, cos)
let kosinus : odvedljiva = (cos, fun x -> -.sin x)
let eksp : odvedljiva = (exp, exp)

let ( ++. ) : odvedljiva -> odvedljiva -> odvedljiva =
 (* pozorni bodite, da anonimni funkciji v paru date med oklepaje *)
 fun (f, f') (g, g') -> ((fun x -> f x +. g x), fun x -> f' x +. g' x)

(* let primer_3_12 =
   let _, f' = sinus ++. kosinus ++. eksp in
   f' 1. *)

(** Vrednost odvoda *)

let vrednost : odvedljiva -> float -> float=
   fun (f,_) arg -> f arg
   
let odvod : odvedljiva -> float -> float= 
   fun (_, f')  arg -> f' arg

(** Osnovne funkcije *)

let konstanta  : float -> odvedljiva = 
   fun c-> ((fun _ -> c), fun _ -> 0.)
let identiteta :odvedljiva = ((fun x -> x), fun _ -> 1.)

(** Produkt in kvocient *)

let ( **. )  : odvedljiva -> odvedljiva -> odvedljiva  = 
   fun (f, f')(g, g') -> ((fun x -> f x *. g x), (fun x -> f' x *. g x +. g' x *. f x))
let ( //. ) : odvedljiva -> odvedljiva -> odvedljiva= 
   fun (f, f') (g, g') -> ((fun x ->  f x /. g x), (fun x -> (f' x *. g x -. g' x *. f x) /. (g x *. g x)))
      
let kvadrat = identiteta **. identiteta 

(** Kompozitum *)

let ( @@. ): odvedljiva -> odvedljiva -> odvedljiva = 
   fun (f, f') (g, g') -> ((fun x -> f (g x)), (fun x -> f' (g x) *. g' x))
(* let vedno_ena = (kvadrat @@. sinus) ++. (kvadrat @@. kosinus) *)
(* let primer_4_1 = vrednost vedno_ena 12345. *)
(* let primer_4_2 = odvod vedno_ena 12345. *)

(* ## Substitucijska šifra *)
let abeceda = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
let quick_brown_fox = "THEQUICKBRWNFXJMPSOVLAZYDG"
let rot13 = "NOPQRSTUVWXYZABCDEFGHIJKLM"
let indeks c = Char.code c - Char.code 'A'
let crka i = Char.chr (i + Char.code 'A')

(** Šifriranje *)
let sifriraj sifra besedilo = 
   let pomozna znak=
      if String.contains abeceda znak then 
         let indeks = String.index abeceda znak in
         sifra.[indeks]
      else znak 
   in
   String.map pomozna besedilo
(* let primer_5_1 = sifriraj quick_brown_fox "HELLO, WORLD!" *)
(* let primer_5_2 = "VENI, VIDI, VICI" |> sifriraj rot13 *)
(* let primer_5_3 = "VENI, VIDI, VICI" |> sifriraj rot13 |> sifriraj rot13 *)

(** Inverzni ključ *)

let inverz sifra  = 
   let pomozna znak = 
      if String.contains abeceda znak then 
         let indeks = String.index sifra znak in
         abeceda.[indeks]
      else znak
   in
   String.map pomozna abeceda

(* let primer_5_4 = inverz quick_brown_fox *)
(* let primer_5_5 = inverz rot13 = rot13 *)
(* let primer_5_6 = inverz "BCDEA" *)

(** Ugibanje ključa *)

let besede =
  "the of to and a in is it you that he was for on are with as i his they be \
   at one have this from or had by word but what some we can out other were \
   all there when up use your how said an each she which do their time if will \
   way about many then them write would like so these her long make thing see \
   him two has look more day could go come did number sound no most people my \
   over know water than call first who may down side been now find any new \
   work part take get place made live where after back little only round man \
   year came show every good me give our under name very through just form \
   sentence great think say help low line differ turn cause much mean before \
   move right boy old too same tell does set three want air well also play \
   small end put home read hand port large spell add even land here must big \
   high such follow act why ask men change went light kind off need house \
   picture try us again animal point mother world near build self earth father \
   head stand own page should country found answer school grow study still \
   learn plant cover food sun four between state keep eye never last let \
   thought city tree cross farm hard start might story saw far sea draw left \
   late run don't while press close night real life few north open seem \
   together next white children begin got walk example ease paper group always \
   music those both mark often letter until mile river car feet care second \
   book carry took science eat room friend began idea fish mountain stop once \
   base hear horse cut sure watch color face wood main enough plain girl usual \
   young ready above ever red list though feel talk bird soon body dog family \
   direct pose leave song measure door product black short numeral class wind \
   question happen complete ship area half rock order fire south problem piece \
   told knew pass since top whole king space heard best hour better true . \
   during hundred five remember step early hold west ground interest reach \
   fast verb sing listen six table travel less morning ten simple several \
   vowel toward war lay against pattern slow center love person money serve \
   appear road map rain rule govern pull cold notice voice unit power town \
   fine certain fly fall lead cry dark machine note wait plan figure star box \
   noun field rest correct able pound done beauty drive stoDo contain front \
   teach week final gave green oh quick develop ocean warm free minute strong \
   special mind behind clear tail produce fact street inch multiply nothing \
   course stay wheel full force blue object decide surface deep moon island \
   foot system busy test record boat common gold possible plane stead dry \
   wonder laugh thousand ago ran check game shape equate hot miss brought heat \
   snow tire bring yes distant fill east paint language among grand ball yet \
   wave drop heart am present heavy dance engine position arm wide sail \
   material size vary settle speak weight general ice matter circle pair \
   include divide syllable felt perhaps pick sudden count square reason length \
   represent art subject region energy hunt probable bed brother egg ride cell \
   believe fraction forest sit race window store summer train sleep prove lone \
   leg exercise wall catch mount wish sky board joy winter sat written wild \
   instrument kept glass grass cow job edge sign visit past soft fun bright \
   gas weather month million bear finish happy hope flower clothe strange gone \
   jump baby eight village meet root buy raise solve metal whether push seven \
   paragraph third shall held hair describe cook floor either result burn hill \
   safe cat century consider type law bit coast copy phrase silent tall sand \
   soil roll temperature finger industry value fight lie beat excite natural \
   view sense ear else quite broke case middle kill son lake moment scale loud \
   spring observe child straight consonant nation dictionary milk speed method \
   organ pay age section dress cloud surprise quiet stone tiny climb cool \
   design poor lot experiment bottom key iron single stick flat twenty skin \
   smile crease hole trade melody trip office receive row mouth exact symbol \
   die least trouble shout except wrote seed tone join suggest clean break \
   lady yard rise bad blow oil blood touch grew cent mix team wire cost lost \
   brown wear garden equal sent choose fell fit flow fair bank collect save \
   control decimal gentle woman captain practice separate difficult doctor \
   please protect noon whose locate ring character insect caught period \
   indicate radio spoke atom human history effect electric expect crop modern \
   element hit student corner party supply bone rail imagine provide agree \
   thus capital won't chair danger fruit rich thick soldier process operate \
   guess necessary sharp wing create neighbor wash bat rather crowd corn \
   compare poem string bell depend meat rub tube famous dollar stream fear \
   sight thin triangle planet hurry chief colony clock mine tie enter major \
   fresh search send yellow gun allow print dead spot desert suit current lift \
   rose continue block chart hat sell success company subtract event \
   particular deal swim term opposite wife shoe shoulder spread arrange camp \
   invent cotton born determine quart nine truck noise level chance gather \
   shop stretch throw shine property column molecule select wrong gray repeat \
   require broad prepare salt nose plural anger claim continent oxygen sugar \
   death pretty skill women season solution magnet silver thank branch match \
   suffix especially fig afraid huge sister steel discuss forward similar \
   guide experience score apple bought led pitch coat mass card band rope slip \
   win dream evening condition feed tool total basic smell valley nor double \
   seat arrive master track parent shore division sheet substance favor \
   connect post spend chord fat glad original share station dad bread charge \
   proper bar offer segment slave duck instant market degree populate chick \
   dear enemy reply drink occur support speech nature range steam motion path \
   liquid log meant quotient teeth shell neck"

let slovar = [ (* TODO *) ]
(* let primer_5_7 = take 42 slovar *)
(* let primer_5_8 = List.nth slovar 321 *)

(* Med ugibanjem seveda ne bomo poznali celotnega ključa. V tem primeru bomo za neznane črke uporabili znak `_`. Na primer, če bi vedeli, da je črka `A` v besedilu šifrirana kot `X`, črka `C` pa kot `Y`, bi ključ zapisali kot `"X_Y_______________________"`. *)
(*  *)
(* Napišite funkcijo `dodaj_zamenjavo : string -> char * char -> string option`, ki sprejme ključ ter ga poskusi razširiti z zamenjavo dane črke. Funkcija naj vrne `None`, če razširitev vodi v ključ, ki ni bijektiven (torej če ima črka že dodeljeno drugo zamenjavo ali če smo isto zamenjavo dodelili dvema različnima črkama). *)

(** Razširjanje ključa s črko *)
let dodaj_zamenjavo _ _ = failwith __LOC__

(* let primer_5_9 = dodaj_zamenjavo "AB__E" ('C', 'X') *)
(* let primer_5_10 = dodaj_zamenjavo "ABX_E" ('C', 'X') *)
(* let primer_5_11 = dodaj_zamenjavo "ABY_E" ('C', 'E') *)

(** Razširjanje ključa z besedo *)

(* S pomočjo funkcije `dodaj_zamenjavo` sestavite še funkcijo `dodaj_zamenjave : string -> string * string -> string option`, ki ključ razširi z zamenjavami, ki prvo besedo preslikajo v drugo. *)

let dodaj_zamenjave _ _ = failwith __LOC__
(* let primer_5_12 = dodaj_zamenjave "__________________________" ("HELLO", "KUNNJ") *)
(* let primer_5_13 = dodaj_zamenjave "ABCDU_____________________" ("HELLO", "KUNNJ") *)
(* let primer_5_14 = dodaj_zamenjave "ABCDE_____________________" ("HELLO", "KUNNJ") *)

(** Vse možne razširitve *)

(* Sestavite funkcijo `mozne_razsiritve : string -> string -> string list -> string list`, ki vzame ključ, šifrirano besedo ter slovar vseh možnih besed, vrne pa seznam vseh možnih razširitev ključa, ki šifrirano besedo slikajo v eno od besed v slovarju. *)

let mozne_razsiritve _ _ _ = failwith __LOC__

(* let primer_5_15 =
   slovar
   |> mozne_razsiritve (String.make 26 '_') "KUNNJ"
   |> List.map (fun kljuc -> (kljuc, sifriraj kljuc "KUNNJ")) *)

(** Odšifriranje *)

(* Napišite funkcijo `odsifriraj : string -> string option`, ki sprejme šifrirano besedilo in s pomočjo slovarja besed ugane odšifrirano besedilo. Funkcija naj vrne `None`, če ni mogoče najti nobenega ustreznega ključa. *)
let odsifriraj _ = failwith __LOC__
(* let primer_5_16 = sifriraj quick_brown_fox "THIS IS A VERY HARD PROBLEM" *)
(* let primer_5_17 = odsifriraj "VKBO BO T AUSD KTSQ MSJHNUF" *)
