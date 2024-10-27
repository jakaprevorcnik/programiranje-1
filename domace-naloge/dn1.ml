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
        
    

    
              