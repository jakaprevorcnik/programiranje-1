set_option autoImplicit false

/------------------------------------------------------------------------------
 ## Naravna števila

 Definirajte funkcijo, ki _rekurzivno_ (torej naivno in ne direktno s formulo,
 ki jo boste morali dokazati) sešteje prvih `n` naravnih števil, ter
 dokažite, da zanjo velja znana enakost (najprej v obliki, ki ne zahteva
 deljenja, nato pa še v običajni obliki).
------------------------------------------------------------------------------/
def vsota_prvih : Nat -> Nat :=
  fun n =>
    match n with
     | 0 => 0
     | n' +  1 => n'  + 1 + vsota_prvih (n') -- ce uporabim n' in (n' -1) v argumentu funkcije se nekaj pritozuje


theorem gauss  {n : Nat} : 2 * vsota_prvih n = n * (n + 1) :=
  by
    induction n with
    | zero => simp [vsota_prvih]
    | succ n' ih =>
      simp [vsota_prvih]
      rw [Nat.mul_add, ih, ←Nat.right_distrib, Nat.mul_comm,
        Nat.add_comm 2 n', Nat.add_assoc n' 1 1]


theorem cisto_pravi_gauss {n : Nat} : vsota_prvih n = (n * (n + 1)) / 2 :=
  by
    induction n with
    | zero => simp [vsota_prvih]
    | succ n' ih =>
      simp [vsota_prvih]
      rw [ih, Nat.add_comm n' 1] --potrebno je se izpostavit 1 + n


/------------------------------------------------------------------------------
 ## Vektorji

 Definirajmo vektorje podobno kot na predavanjih, le da namesto svojih naravnih
 števil uporabimo vgrajena. Da se tipi ujamejo, funkcijo stikanja napišemo s
 pomočjo taktik.

 Napišite funkcijo `obrni`, ki vrne na glavo obrnjen vektor, ter funkciji
 `glava` in `rep`, ki varno vrneta glavo in rep _nepraznega_ seznama.
------------------------------------------------------------------------------/

inductive Vektor : Type → Nat → Type where
  | prazen : {A : Type} → Vektor A 0
  | sestavljen : {A : Type} → {n : Nat} → A → Vektor A n → Vektor A (n + 1)
deriving Repr

def stakni : {A : Type} → {m n : Nat} → Vektor A m → Vektor A n → Vektor A (m + n) :=
  fun xs ys => match xs with
  | .prazen => by rw [Nat.add_comm]; exact ys
  | .sestavljen x xs' => by rw [Nat.add_right_comm]; exact Vektor.sestavljen x (stakni xs' ys)

-- Pomožna funkcija za dodajanje elementa na konec vektorja
def dodaj_na_konec {A : Type} : {n : Nat} → A → Vektor A n → Vektor A (n + 1) :=
  fun a xs => match xs with
  | .prazen => .sestavljen a .prazen
  | .sestavljen x xs => .sestavljen x (dodaj_na_konec a xs)

def obrni : {A : Type} → {n : Nat} → Vektor A n → Vektor A n :=
  fun xs => match xs with
  |.prazen => .prazen
  |.sestavljen x xs => dodaj_na_konec x (obrni xs)


def glava : {A : Type} → List A → A :=
  fun xs => match xs with
  | [] => sorry --zeleli bi da javi napako
  | x :: _ => x


def rep : {A : Type} → List A → List A :=
  fun xs => match xs with
  | [] => []
  | _ :: xs' => xs'

/------------------------------------------------------------------------------
 ## Predikatni račun

 Dokažite spodnje tri trditve. Zadnja je _paradoks pivca_, ki pravi:
   "V vsaki neprazni gostilni obstaja gost, za katerega velja,
   da če pije on, pijejo vsi v gostilni."
 Za dokaz potrebujete klasično logiko, torej nekaj iz modula `Classical`.
------------------------------------------------------------------------------/

theorem forall_implies : {A : Type} → {P Q : A → Prop} →
  (∀ x, (P x → Q x)) → (∀ x, P x) → (∀ x, Q x) :=
  by
    intros A P Q h1 h2 x
    apply h1
    apply h2



theorem forall_implies' : {A : Type} → {P : Prop} → {Q : A → Prop} →
  (∀ x, (P → Q x)) ↔ (P → ∀ x, Q x) :=
  by
    intros A P Q
    constructor
    intros x h1 h2
    apply  x
    exact h1
    intros a q p
    apply a
    exact p



theorem paradoks_pivca :
  {G : Type} → {P : G → Prop} →
  (g : G) →  -- (g : G) pove, da je v gostilni vsaj en gost
  ∃ (p : G), (P p → ∀ (x : G), P x) :=
  by
    intros G P g
    constructor
    intro h
    intro x
    --ne znam zdruziti predpostavk da bi dobil Px





/------------------------------------------------------------------------------
 ## Dvojiška drevesa

 Podan naj bo tip dvojiških dreves skupaj s funkcijama za zrcaljenje in izračun
 višine ter dvema funkcijama, ki obe od leve proti desni naštejeta elemente
 drevesa. Pri tem prva deluje naivno in ima časovno zahtevnost O(n log n), druga
 pa je malo bolj zapletena in deluje v času O(n). Dokažite spodnje enakosti, pri
 čemer lahko do pomožne funkcije `aux` dostopate kot `elementi'.aux`
-------------------------------------------------------------------------------/

inductive Drevo : Type → Type where
  | prazno : {A : Type} → Drevo A
  | sestavljeno : {A : Type} → Drevo A → A → Drevo A → Drevo A

def zrcali : {A : Type} → Drevo A → Drevo A :=
  fun t => match t with
  | .prazno => .prazno
  | .sestavljeno l x d => .sestavljeno (zrcali d) x (zrcali l)

def visina : {A : Type} → Drevo A → Nat :=
  fun t => match t with
  | .prazno => 0
  | .sestavljeno l _ d => 1 + max (visina l) (visina d)

def elementi : {A : Type} → Drevo A → List A :=
  fun t => match t with
  | .prazno => []
  | .sestavljeno l x d => elementi l ++ x :: elementi d

def elementi' : {A : Type} → Drevo A → List A :=
  let rec aux : {A : Type} → Drevo A → List A → List A :=
    fun t acc => match t with
    | .prazno => acc
    | .sestavljeno l x d => aux l (x :: aux d acc)
  fun t => aux t []

theorem zrcali_zrcali
  {A : Type}  (t : Drevo A) :
  zrcali (zrcali t) = t :=
  by
    induction t with
    | prazno => simp [zrcali]
    | sestavljeno t' x d ih1 ih2 =>
      simp [zrcali]
      rw [ih1, ih2]
      constructor
      rfl
      rfl




theorem visina_zrcali
  {A : Type} (t : Drevo A) :
  visina (zrcali t) = visina t :=
  by
    induction t with
    | prazno => simp[visina, zrcali]
    | sestavljeno t' x d ih1 ih2 =>
      simp [zrcali, visina]
      rw [ih1, ih2]
      rw [Nat.max_comm]

theorem elementi_elementi'
  {A : Type}  (t : Drevo A) :
  elementi t = elementi' t :=
  by
    induction t with
    | prazno => simp [elementi', elementi, elementi'.aux]
    | sestavljeno l x d ihl ihd =>
      simp [elementi, elementi']
      rw [ihl, ihd]
      simp [elementi'.aux]
      --potrebno se je znebiti ++
