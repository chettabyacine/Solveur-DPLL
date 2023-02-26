open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"


(********************************************************************)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)
   let simplifie l clauses =
    (* premiere fonction auxiliere :
        clause_avec_l : int -> int list list -> int list list 
        Suprime toutes les clauses qui contiennent le litereau "ltro"
    *)
    let clause_avec_l  ltro formule =
      let rec aux formule reslt =
        match formule with
        | []   -> reslt (*Si une clauses est vide en retourne la lise vide*)
          (*sinon on verifie dans chaque clauses si la clause contient ltro *)
        | h::t -> match ((fun c -> if(List.mem (ltro) c) then None else Some c ) h) with(* h represente une clause*)
          | None   -> aux t reslt   (*si h ne contient pas ltro on retourne None*)
          | Some e -> aux t (e::reslt)  (*si h contient pas "ltro" (Some e represente ltro)*)
      in aux formule []
      (* deuxieme fonction auxiliere :
        clause_avec_non_l : int -> int list list -> int list list 
        Suprime toutes les clauses qui contiennent le litereau "ltro"
    *)
    in let clause_avec_non_l  ltro formule =(*Suprime le litereau "ltro" dans toutes les clauses *)
         let rec aux formule reslt =
           match formule with
           | []   -> reslt(*Si une clauses est vide en retourne la lise vide*)
           (*sinon on verifie dans chaque clauses si la clause contient (-ltro) alor on le suprime de la clause *)
           | a::t -> match (
                              let filtre h =(*  fonction filtre : 
                                              suprime le litereau (-ltro) dans une clauses qui le contient et renvois la clause apres supression 
                                              sinon renvoi la meme clause si elle contient pas (-ltro)
                                           *)
                                if(h=[]) then None
                                else if (List.mem (-ltro) h) then ( let rec suprm e l =
                                                                      let rec aux l acc = match l with
                                                                        | [] -> Some acc
                                                                        | a::b -> if a = e then (aux b acc)
                                                                            else (aux b (a::acc))
                                                                      in if l = [] then None else aux l []
                                                                    in suprm (-ltro) h
                                                                  )
                                else  Some(h)
                              in filtre a
                            )with
                            | None   -> aux t reslt
                            | Some e -> aux t (e::reslt)
         in aux formule []
    in clause_avec_non_l l (clause_avec_l l clauses);;(*On enleve toute les clauses qui contienent 'l'. puis on enleve 'l' de toutes les clause qui reste*)
  

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche




    
(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)

    let  unitaire clauses =
    let rec aux clauses =
      match clauses with
      | [] -> 0 (* 0 represente le literral null*)
      | a::l-> if(List.tl a = []) then (List.hd a )(* si la clause contient un seul element *)
          else aux l
    in aux clauses;;
    

    
  let rec isPur l clauses = match clauses with
  (* tester si l est pur dans clauses*)
    |[]-> true
    |clause::reste -> (List.mem (-1 * l) clause) && (isPur l reste);;


  (* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)
  let pur clauses =
    let rec aux mesclauses = match mesclauses with
      |[]-> 0 
      |clause:: reste -> match clause with
        |[]-> aux reste
        |l::r when (isPur l clauses)-> l
        |l::r when (r=[]) (* when l n'est pas pur et c'est la fin de la liste*)  -> 0 
        |l::r (* when l n'est pas pur et il y  tjr autres éléments à tester*) -> aux (r::reste)
    in aux clauses;;

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation = 
  if (mem [] clauses) then solveur_split clauses interpretation else
    begin
      if( clauses = []) then solveur_split clauses interpretation else
        begin
            let unit = unitaire clauses in
            if(unit!=0) then solveur_dpll_rec (simplifie unit clauses) (unit::interpretation)(*si on trouve unit on simplifie par unit*)
            else
              begin
                let pure = pur clauses in
                if(pure!=0) then solveur_dpll_rec (simplifie pure clauses) (pure::interpretation)(*si on trouve pure on simplifie par pure*)
              else solveur_split clauses interpretation
            end
        end
    end

(* ensembles de clauses de test  *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]];;
 
(*les reintegrer dans le code pour afficher ces tests *)
(**
print_string "exemple_3_12 ";;
let _ = print_modele (solveur_dpll_rec exemple_3_12 []);;
print_string "exemple_7_2 ";;
let _ = print_modele (solveur_dpll_rec exemple_7_2 []);;
print_string "exemple_7_4 ";;
let _ = print_modele (solveur_dpll_rec exemple_7_4 []);;
print_string "exemple_7_8 ";;
let _ = print_modele (solveur_dpll_rec exemple_7_8 []);;
print_string "systeme ";;
let _ = print_modele (solveur_dpll_rec systeme []);;
print_string "coloriage ";;
let _ = print_modele (solveur_dpll_rec coloriage []);;
**)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
