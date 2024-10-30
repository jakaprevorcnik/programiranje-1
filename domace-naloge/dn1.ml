(*------------------OGREVANJE---------------*)

let stevke b n =
    let rec loop n b acc = (*def repno rekurzivno funkcijo*)
        if n = 0 then acc
        else loop (n/b) b (n mod b::acc) in
    match n with           (*locimo primere*)
    | 0 -> [0]
    | _ -> loop n b  []

let rec take n l =
    match n, l with
    | 0, l -> []
    | _, [] -> []
    | n, x::xs -> x::take (n - 1) xs

let rec drop_while f l =
    match l with
    | [] -> []
    | x::xs -> if f x then drop_while f xs else x::xs

let rec filter_mapi f l =
    let rec pomozna f l i =     (*definiramo pomozno funkcijo da imamo tudi indeks kot parameter*)
        match l with
        | [] -> []
        | x::xs -> 
            match f i x with
            | Some y -> y :: pomozna f xs (i+1)
            | None -> pomozna f xs (i+1) in
        pomozna f l 0 (*zacetni indeks bo 0*)
        

 

(*-----------------POLINOMI--------------------*)

let rec pocisti p =
    let rec pocisti_acc p acc =
        let rec vsota list =
            match list with (* zakaj ne dela ce dam function namesto match*)
            | [] -> 0
            | x::xs -> x + vsota xs in
        match p with
        |[] -> []
        | x::xs -> if vsota xs = 0 then x::acc else pocisti_acc xs (x::acc) in
    List.rev (pocisti_acc p []) 

let rec ( +++ ) p q =
    match p, q with
    | [], q -> q
    | p, [] -> p
    | x::xs, y::ys -> pocisti ((x + y)::( +++ ) xs ys)

(*let rec ( *** ) p q =*)

let rec vrednost p arg =
    let rec pomozna p arg i = (*vzamemo kot parameter se index, da dobimo eksponent v clenu polinoma*)
        let rec potenca a b = (*definiramo si funkcijo potenca, ki sprejme osnovo a in eksponent b*)
            if b = 0 then 1 else a * potenca a (b - 1) in
        match p, i with
        | [], i -> 0 
        | x::xs, i -> x * potenca arg i + pomozna xs arg (i + 1) in (*napisemo vrednost polinoma*)
    pomozna p arg 0

let rec odvod p =   (*kako se znebiti nicle spredaj*)
    let rec pomozna p i =
        match p, i with
        | [], i -> []
        | x::xs, i -> x * i:: pomozna xs (i + 1) in
    pomozna p 0 (*??ali je boljse s function ali brez??*)
 
let rec izpis p =
    let rec pomozna p i =
        let superscript n =
            match n with
            | 0 -> "" | 1 -> "" | 2 -> "²" | 3 -> "³" | 4 -> "⁴"
            | 5 -> "⁵" | 6 -> "⁶" | 7 -> "⁷" | 8 -> "⁸" | 9 -> "⁹"
            | _ -> "^" ^ string_of_int n in
        match List.rev p , i with
        | [], i -> ""
        | x::xs, 0 -> string_of_int x ^ " " ^  "+" ^ " " ^ pomozna xs (i + 1)
        | x::xs, i -> string_of_int x ^ "x" ^ superscript i ^ " " ^  "+" ^ " " ^ pomozna xs (i + 1) in
    pomozna p 0