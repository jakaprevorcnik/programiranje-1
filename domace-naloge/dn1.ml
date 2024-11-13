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
            match list with 
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
    pomozna p 0 
 
let rec izpis p = (*treba je se popravit za negativna stevila*)
    let rec pomozna p i =
        let superscript n =
            match n with
            | 0 -> "" | 1 -> "" | 2 -> "²" | 3 -> "³" | 4 -> "⁴"
            | 5 -> "⁵" | 6 -> "⁶" | 7 -> "⁷" | 8 -> "⁸" | 9 -> "⁹"
            | _ -> "^" ^ string_of_int n in
        match p, i with
        | [], i -> ""
        | x::xs, 0 -> if x = 0 then pomozna xs (i + 1) else
             string_of_int x ^ " " ^  "+" ^ " " ^ pomozna xs (i + 1)
        | x::xs, i -> if x = 1 then "x" ^ superscript i ^ " " ^  "+" ^ " " ^ pomozna xs (i + 1) else (*locimo primer, ko koef = 1*)
            string_of_int x ^ "x" ^ superscript i ^ " " ^  "+" ^ " " ^ pomozna xs (i + 1) in
    pomozna p 0

(*--------------------------IZOMORFIZMI MNOZIC-------------------------------------*)

let phi1  =
    function
    | (a, b) -> (b, a)

let psi1  =
    function
    | (b, a) -> (a, b)

(*najprej definiramo prvo in drugo injekcijo*)
type ('a, 'b) sum = In1 of 'a | In2 of 'b 
(*zapisemo bijekcji*)
let phi2 =
    function
    | In1 a -> In2 a
    | In2 b -> In1 b

let psi2 =
    function
    | In1 b -> In2 b
    | In2 a -> In1 a

let phi3 =
    function (a, (b, c)) -> ((a, b), c)

let psi3 = 
    function ((a,b), c) -> (a, (b,c))

let phi4 =
    function
    | In1 a->  In1 (In1 a)
    | In2 (In2 c) -> In2 c
    | In2 (In1 b) -> In1 (In2 b)

let psi4 =
    function
    | In1 (In1 a) -> In1 a 
    | In2 c -> In2 (In2 c)
    | In1 (In2 b) -> In2 (In1 b)
let phi5 =
    function 
    | (a, In1 b) -> In1 (a, b)
    | (a, In2 c) -> In2 (a, c)
    
let psi5 =
    function 
    | In1 (a, b) -> (a, In1 b)
    | In2 (a, c) -> (a, In2 c)
   

let phi6 f = 
    fun x -> (f (In1 x), f (In2 x))

let psi6 (f, g) =
    function
    | In1 x -> f x
    | In2 x -> g x

let psi6 (f, g) = 
    (fun x -> (f x, g x))

let psi7 f =
    fun x -> (fst(f x), snd(f x))
 




(*--------------------------SAMODEJNO ODVAJANJE-----------------------------------*)

(*import ---------------------------------------------*)
type odvedljiva = (float -> float) * (float -> float)

let sinus : odvedljiva = (sin, cos)
let kosinus : odvedljiva = (cos, (fun x -> -. sin x))
let eksp : odvedljiva = (exp, exp)
let ( ++. ) : odvedljiva -> odvedljiva -> odvedljiva =
  (* pozorni bodite, da anonimni funkciji v paru date med oklepaje *)
  fun (f, f') (g, g') -> ((fun x -> f x +. g x), (fun x -> f' x +. g' x))
(*------------------------------------------------------------------------------*)

let vrednost : odvedljiva -> float -> float =
    fun (f, f') -> (fun x -> f x)

let odvod : odvedljiva -> float -> float =
    fun (f, f') -> (fun x -> f' x)

let konstanta (c : float) : odvedljiva =
    ((fun x -> c), (fun x -> 0.))

let identiteta x : odvedljiva =
    ((fun x -> x), (fun x -> 1.))

let ( **. ) : odvedljiva -> odvedljiva -> odvedljiva =
    fun (f, f') (g, g') -> 
        ((fun x -> f x *. g x), (fun x -> f' x *. g x +. f x *. g' x))

let ( //. ) : odvedljiva -> odvedljiva -> odvedljiva =
fun (f, f') (g, g') -> 
    ((fun x -> f x /. g x), (fun x -> (f' x *. g x -. f x *. g' x) /. (g x *. g x)))

let ( @@. ) : odvedljiva -> odvedljiva -> odvedljiva =
fun (f, f') (g, g') -> 
    ((fun x -> f(g x)), (fun x -> f'(g x) *. g' x))
     

(*---------------------------SUBSTITUCIJSKA SIFRA----------------------------------*)

(*import : indeks in crka*)
let indeks c = Char.code c - Char.code 'A'
let crka i = Char.chr (i + Char.code 'A') 
(*--------------------------------------*)


let odsifriraj : string -> string option =



    