open Lambda


(* message de présentation *)

let () = Printf.printf "\n\n-------------------------------\n"; 
	 Printf.printf "      interface cool       \n";
	 Printf.printf "-------------------------------\n"; 
	 Printf.printf "\n\n Entrer un type à prouver:     \n"

(*lecture de la preuve *)
let type_to_proove = read_line ()

let rec main finish =
  match finish with
  | 1 -> let () = Printf.printf "\nput your next tactique\n"  in
     let tactic = read_line () in
	 let () = Printf.printf "%s" tactic in
	 (* ici j'appliquerai la tactique *)
	 if true 
	 then main 1
	 else main 0
  | _ -> ()

let () = main 1

		       
