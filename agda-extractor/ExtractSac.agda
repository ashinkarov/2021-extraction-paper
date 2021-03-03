open import Structures
open import SacTy

module ExtractSac where
open import Data.String as S hiding (_++_) renaming (_≟_ to _≟s_)
open import Data.List as L hiding (_++_)
open import Data.List.Categorical
open import Data.List.Properties as L
open import Data.Nat as N
open import Agda.Builtin.Nat using (div-helper; mod-helper)

open import Data.Nat.Properties as N
open import Data.Nat.Show renaming (show to showNat)
open import Data.Product as Σ hiding (map)
open import Data.Sum hiding (map)
open import Data.Vec as V using (Vec; [] ; _∷_)
open import Data.Char using (Char) renaming (_≈?_ to _c≈?_)
open import Data.Bool
open import Data.Fin as F using (Fin; zero; suc; inject₁; fromℕ<; #_)
open import Data.Maybe as M using (Maybe; just; nothing)
open import Data.Unit

open import Category.Monad
open import Category.Monad.State

open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)

open import Reflection hiding (return; _>>=_; _>>_)
open import Reflection.Term
import      Reflection.Name as RN
open import Reflection.Annotated
open import Reflection.Universe
open import Reflection.Annotated.Free

open import Function

open import Array.Base
open import Array.Properties
open import APL2 using (reduce-1d; _↑_; _↓_; ▴_; ▾_; _-↑⟨_⟩_; _↑⟨_⟩_)

open import Agda.Builtin.Float

open RawMonad ⦃ ... ⦄


-- Glorified sigma type for variable-type pairs
record VarTy : Set where
  constructor _∈_~_
  field v : String
        s : Err SacTy
        t : Arg Type

-- Glorified sigma type for variable-assertion pairs
record Assrt : Set where
  constructor mk
  field v : String
        a : String

Assrts = List Assrt

-- The state used when traversing a Pi type.
record PS : Set where
  field
    cnt : ℕ           -- The source of unique variable names
    cur : String      -- Current variable name (used to collect assertions from its type)
    ctx : List VarTy  -- Names in the telscopes to resolve deBruijn indices
    ret : String      -- Variable that the function returns as a result.
                      -- We assume that there is always a single variable and its name
                      -- is known upfront.  We need this to generate assertions from the
                      -- return type.
    assrts : Assrts   -- Assertions that we generate per each variable.
    kst : KS          -- Compilation state (in case we have to extract some functions used in types)


defaultPS : PS
defaultPS = record { cnt = 1
                   ; cur = ""
                   ; ctx = []
                   ; ret = "__ret"
                   ; assrts = []
                   ; kst = defaultKS
                   }

-- Pack the information about new variables generated
-- by patterns in the clause, assignments to these,
-- and the list of conditions for "getting into" the
-- clause.  E.g.
--   foo : List ℕ → ℕ
--   foo (x ∷ xs) 2 = ...
--
-- Assume that we named top-level arguments [a, b]
-- Then, new variables for this clause are going to be
--     [x, xs]
-- Assignments are:
--     [x = hd a, xs = tl a]
-- Conditions are:
--     [is-cons a, b == 2]
--
-- `cnt` is merely a source of fresh variables.
record PatSt : Set where
  constructor mk
  field
    vars    : List (String × ℕ) --Strings
    assigns : Strings
    conds   : Strings
    cnt     : ℕ
    absrd   : Bool

defaultPatSt : Bool → PatSt
defaultPatSt b = mk [] [] [] 1 b

defaultClausePatSt = defaultPatSt false
defaultAbsurdPatSt = defaultPatSt true

SPS = State PS

-- The main function kit to extract sac functions.
kompile-fun    : Type → Term → Name → SKS Prog
kompile-pi     : Type → SPS (Err SacTy) --Prog
kompile-cls    : Clauses → (vars : Strings) → (ret : String) → SKS Prog
kompile-clpats : Telescope → (pats : List $ Arg Pattern) → (vars : Strings) → PatSt → Err PatSt
{-# TERMINATING #-}
kompile-term   : Term → {- (varctx : Strings) -} {- List VarTy -} Telescope → SKS Prog


-- Normalise the name of the symbols (functions, constructors, ...)
-- that we obtain from showName, i.e. remove dots, replace weird
-- symbols with ascii.
nnorm : String → String
nnorm s = replace '.' "_"
        $ replace '-' "_"
        $ replace '+' "plus"
        $ replace 'α' "alpha"
        $ replace 'ω' "omega"
        $ replace '→' "to"
        $ s
  where
    repchar : (from : Char) (to : String) (x : Char) → String
    repchar from to x with does $ x c≈? from
    ... | true  = to
    ... | false = fromList (x ∷ [])

    replace : (from : Char) (to : String) → String → String
    replace f t s = "" ++/ L.map (repchar f t) (toList s)


private
  kf : String → Prog
  kf x = error $ "kompile-fun: " ++ x

  validate-ty : Err SacTy → Prog
  validate-ty (error x) = error x
  validate-ty (ok τ) = let τ′ = sacty-normalise τ in
                       case nested? τ′ of λ where
                         hom → ok $ sacty-to-string τ′
                         nes → error $ "sac does not support nested types, but `"
                                    ++ sacty-to-string τ′ ++ "` found"

  module R = RawMonadState (StateMonadState KS)

kompile-fun ty (pat-lam [] []) n =
  return $ kf "got zero clauses in a lambda term"
kompile-fun ty (pat-lam cs []) n = do
  kst ← R.get
  let (rt , ps) = kompile-pi ty $ record defaultPS{ kst = kst }
      rt = validate-ty rt
      rv = PS.ret ps
      ns = showName n
      args = ok ", " ++/ L.map (λ where (v ∈ t ~ _) → validate-ty t ⊕ " " ⊕ v) (PS.ctx ps)
      ret-assrts = list-filter (λ where (mk v _) → v ≈? rv) $ PS.assrts ps
      arg-assrts = list-filter (dec-neg λ where (mk v _) → v ≈? rv) $ PS.assrts ps
      assrt-to-code = ("/* " ++_) ∘ (_++ " */") ∘ Assrt.a
  R.put $ PS.kst ps
  --b ← if does (showName n S.≟ "Example-02.testn") then kompile-cls cs (L.map (λ where (v ∈ _ ~ _) → v) $ PS.ctx ps) rv else (return $ ok "XX")
  b ← kompile-cls cs (L.map (λ where (v ∈ _ ~ _) → v) $ PS.ctx ps) rv
  return $ "// Function " ⊕ ns ⊕ "\n"
         ⊕ rt ⊕ "\n"
         ⊕ nnorm ns ⊕ "(" ⊕ args ⊕ ") {\n"
         ⊕ "\n" ++/ L.map assrt-to-code arg-assrts
         ⊕ rt ⊕ " " ⊕ rv ⊕ ";\n"
         ⊕ b -- function body
         ⊕ "\n" ++/ L.map assrt-to-code ret-assrts
         ⊕ "return " ⊕ rv ⊕ ";\n"
         ⊕ "}\n\n"

kompile-fun _ _ _ =
  return $ kf "expected pattern-matching lambda"


private
  kp : ∀ {X} → String → SPS (Err X)
  kp x = return $ error $ "kompile-pi: " ++ x

  ke : ∀ {X} → String → SPS (Err X)
  ke x = return $ error x

  module P = RawMonadState (StateMonadState PS)

  infixl 10 _p+=c_ _p+=a_
  _p+=c_ : PS → ℕ → PS
  ps p+=c n = record ps{ cnt = PS.cnt ps + n }

  _p+=a_ : PS → Assrt → PS
  ps p+=a a = record ps{ assrts = a ∷ PS.assrts ps }

  ps-fresh : String → SPS String
  ps-fresh x = do
    ps ← P.get
    P.modify (_p+=c 1)
    return $ x ++ showNat (PS.cnt ps)

  lift-ks : ∀ {X} → SKS X → SPS X
  lift-ks xf sps = let (x , sks) = xf (PS.kst sps) in x , record sps {kst = sks}

  sps-kompile-term : Term → SPS Prog
  sps-kompile-term t = do
    ps ← P.get
    lift-ks $ kompile-term t $ (L.map (λ where (v ∈ _ ~ t) → (v , t)) $ PS.ctx ps)


kompile-ty : Type → (pi-ok : Bool) → SPS (Err SacTy)
kompile-ty (Π[ s ∶ arg i x ] y) false = kp "higher-order functions are not supported"
kompile-ty (Π[ s ∶ arg i x ] y) true  = do
    v ← ps-fresh "x_"
    P.modify λ k → record k { cur = v }
    (ok t) ← kompile-ty x false
      where e → return e
    P.modify λ k → record k { cur = PS.ret k  -- In case this is a return type
                            ; ctx = PS.ctx k ++ [ v ∈ ok t ~ arg i x ] }
    kompile-ty y true

kompile-ty (con c args) pi-ok =
  kp $ "don't know how to handle `" ++ showName c ++ "` constructor"
kompile-ty (def (quote ℕ) args) _ = return $ ok int
kompile-ty (def (quote Bool) args) _ = return $ ok bool
kompile-ty (def (quote Float) args) _ = return $ ok float
kompile-ty (def (quote Fin) (arg _ x ∷ [])) _ = do
  ok p ← sps-kompile-term x where error x → ke x
  v ← PS.cur <$> P.get
  P.modify $ _p+=a (mk v $′ "assert (" ++ v ++ " < " ++ p ++ ")")
  return $ ok int

kompile-ty (def (quote L.List) (_ ∷ arg _ ty ∷ _)) _ = do
  el ← ps-fresh "el_"
  v , as ← < PS.cur , PS.assrts > <$> P.get
  -- Any constraints that the subsequent call would
  -- generate will be constraints about the elements
  -- of the list.
  P.modify λ k → record k { cur = el ; assrts = [] }
  ok τ ← kompile-ty ty false where e → return e
  P.modify λ k → record k {
    cur = v;
    assrts = as ++ (L.map {B = Assrt} (λ where (mk _ a) → mk v ("foreach-v (" ++ el ++ ", " ++ v ++ ", " ++ a ++ ")")) $ PS.assrts k)
    -- No need to modify context, as we don't allow higher order functions, so it stays the same.
    }
  return $ ok $ akd nes τ (error "lists do not have static shape") 1

kompile-ty (def (quote V.Vec) (_ ∷ arg _ ty ∷ arg _ n ∷ [])) _ = do
  el ← ps-fresh "el_"
  v , as ← < PS.cur , PS.assrts > <$> P.get
  ok p ← sps-kompile-term n where error x → ke x
  P.modify λ k → record k { cur = el ; assrts = [] }
  ok τ ← kompile-ty ty false where e → return e
  P.modify λ k → record k {
    cur = v;
    assrts = as ++ (L.map {B = Assrt} (λ where (mk _ a) → mk v ("foreach-v (" ++ el ++ ", " ++ v ++ ", " ++ a ++ ")")) $ PS.assrts k)
                ++ [ mk v $′ "assert (shape (" ++ v ++ ")[[0]] == " ++ p ++ ")" ]
    }
  let sh = "[" ⊕ p ⊕ "]"
  case n of λ where
    -- XXX can we possibly miss on any constant expressions?
    (lit (nat n′)) → return $ ok $ aks hom τ sh 1 V.[ n′ ]
    _              → return $ ok $ akd hom τ sh 1


kompile-ty (def (quote Ar) (_ ∷ arg _ el-ty ∷ arg _ dim ∷ arg _ sh ∷ [])) _ = do
  el ← ps-fresh "el_"
  v , as ← < PS.cur , PS.assrts > <$> P.get
  ok d ← sps-kompile-term dim where error x → ke x
  ok s ← sps-kompile-term sh where error x → ke x
  P.modify λ k → record k { cur = el ; assrts = [] }
  ok τ ← kompile-ty el-ty false where e → return e
  P.modify λ k → record k {
    cur = v;
    assrts = as ++ (L.map {B = Assrt} (λ where (mk _ a) → mk v ("foreach-a (" ++ s ++ ", " ++ el ++ ", " ++ v ++ ", " ++ a ++ ")")) $ PS.assrts k)
                ++ [ mk v $′ "assert (take (" ++ d ++ ", shape (" ++ v ++ ")) == " ++ s ++ ")" ]
                -- XXX do we want to assert stuff about rank?
    }
  case dim of λ where
    -- XXX can we possibly miss on any constant expressions?
    -- FIXME consider AKS case here!
    (lit (nat d′)) → return $ ok $ akd hom τ (ok s) d′
    _ → return $ ok $ aud hom τ (ok s)


kompile-ty (def (quote Ix) (arg _ dim ∷ arg _ s ∷ [])) _ = do
  v ← PS.cur <$> P.get
  ok d ← sps-kompile-term dim where error x → ke x
  ok s ← sps-kompile-term s where error x → ke x
  P.modify $ _p+=a (mk v $′ "assert (dim (" ++ v ++ ") == " ++ d ++ ")")
           ∘ _p+=a (mk v $′ "assert (" ++ v ++ " < " ++ s ++ ")")

  case dim of λ where
    (lit (nat d′)) → return $ ok $ aks hom int (ok s) 1 V.[ d′ ]
    _              → return $ ok $ akd hom int (ok s) 1


kompile-ty (def (quote _≡_) (_ ∷ arg _ ty ∷ arg _ x ∷ arg _ y ∷ [])) _ = do
  ok x ← sps-kompile-term x where error x → ke x
  ok y ← sps-kompile-term y where error x → ke x
  v ← PS.cur <$> P.get
  P.modify $ _p+=a (mk v $′ "assert (" ++ x ++ " == " ++ y ++ ")")
  return $ ok unit

kompile-ty (def (quote _≥a_) (_ ∷ _ ∷ arg _ x ∷ arg _ y ∷ [])) _ = do
  ok x ← sps-kompile-term x where error x → ke x
  ok y ← sps-kompile-term y where error x → ke x
  v ← PS.cur <$> P.get
  P.modify $ _p+=a (mk v $′ "assert (" ++ x ++ " >= " ++ y ++ ")")
  return $ ok unit

kompile-ty (def (quote _<a_) (_ ∷ _ ∷ arg _ x ∷ arg _ y ∷ [])) _ = do
  ok x ← sps-kompile-term x where error x → ke x
  ok y ← sps-kompile-term y where error x → ke x
  v ← PS.cur <$> P.get
  P.modify $ _p+=a (mk v $′ "assert (" ++ x ++ " < " ++ y ++ ")")
  return $ ok unit

kompile-ty (def (quote Dec) (_ ∷ arg _ p ∷ [])) _ = do
  _ ← kompile-ty p false
  return $ ok bool



kompile-ty (def n _) _ = kp $ "cannot handle `" ++ showName n ++ "` type"

kompile-ty t _ =
  kp $ "failed with the term `" ++ showTerm t ++ "`"


kompile-pi x = kompile-ty x true




-- The names in the telescopes very oftern are not unique, which
-- would be pretty disasterous if the code generation relies on them.
-- see https://github.com/agda/agda/issues/5048 for more details.
--
-- This function simply ensures that variable names are unique in
-- in the telescope.
tel-rename : Telescope → (db : List (String × ℕ)) → Telescope
tel-rename [] db = []
tel-rename ((v , ty) ∷ tel) db with list-find-el ((_≟s v) ∘ proj₁) db
... | just (_ , n) = (v ++ "_" ++ showNat n , ty)
                     ∷ tel-rename tel (list-update-fst ((_≟s v) ∘ proj₁) db (Σ.map₂ suc))
... | nothing      = (v , ty)
                     ∷ tel-rename tel ((v , 1) ∷ db)


private
  kc : String → SKS Prog
  kc x = return $ error $ "kompile-cls: " ++ x

  _>>=e_ : ∀ {a}{X : Set a} → Err X → (X → SKS Prog) → SKS Prog
  (error s) >>=e _ = return $ error s
  (ok x)    >>=e f = f x

  -- sort in increasing order
  list-sort : ∀ {a}{X : Set a} → (acc l : List (X × ℕ)) → List (X × ℕ)
  list-sort acc [] = acc
  list-sort acc (x ∷ l) = list-sort (insert acc x) l
    where
      insert : _ → _ → _
      insert [] y = y ∷ []
      insert (x ∷ xs) y with proj₂ y N.<? proj₂ x
      ... | yes y<x = y ∷ x ∷ xs
      ... | no  y≥x = x ∷ insert xs y


  isperm : ∀ {a}{X : Set a} → (n max : ℕ) → (db : List ℕ) → List (X × ℕ) → Bool
  isperm 0 0   [] [] = true
  isperm n max db [] = does (1 + max N.≟ n) ∧ does (L.length db N.≟ n)
  isperm n max db ((_ , x) ∷ xs) with list-has-el (N._≟ x) db
  ...                      | true = false
  ...                      | false = isperm n (max N.⊔ x) (x ∷ db) xs

  perm : Telescope → List (String × ℕ) → Err (List String)
  perm tel vs with isperm (L.length tel) 0 [] vs
  ... | false = error $ ", " ++/ L.map (λ where (x , y) → "(" ++ x ++ ", " ++ showNat y ++ ")") vs
                     ++ " is not a permutation of the telescope "
                     ++ showTel tel
  ... | true = ok $ L.reverse $ L.map proj₁ $ list-sort [] vs

  module test-perm where
    test₀ : isperm {X = ℕ} 0 0 [] [] ≡ true
    test₀ = refl

    test₁ : isperm 1 0 [] (("" , 0) ∷ []) ≡ true
    test₁ = refl

    test₂′ : isperm 2 0 [] (("" , 1) ∷ ("" , 0) ∷ []) ≡ true
    test₂′ = refl

    test₃ : isperm 3 0 [] (("" , 2) ∷ ("" , 0) ∷ ("" , 1) ∷ []) ≡ true
    test₃ = refl

    test₄ : isperm 4 0 [] (("" , 2) ∷ ("" , 2) ∷ ("" , 1) ∷ ("" , 3) ∷ []) ≡ false
    test₄ = refl


kompile-tel : Telescope → SPS (Err ⊤)
kompile-tel [] = return $ ok tt
kompile-tel ((v , t@(arg i x)) ∷ tel) = do
  --(ok τ) ← kompile-ty x false where (error x) → return $ error x
  P.modify λ k → record k{ ctx = PS.ctx k ++ [ v ∈ error "?" ~ t ] }
  kompile-tel tel


kompile-cls [] ctx ret = kc "zero clauses found"
kompile-cls (clause tel ps t ∷ []) ctx ret =
  -- Make telscope names unique.
  let tel = (tel-rename $! tel) $! [] in
  kompile-clpats tel ps ctx defaultClausePatSt >>=e λ pst → do
  let (mk vars assgns _ _ _) = pst --in
  t ← kompile-term t $! tel
  let as = "\n" ++/ assgns
  return $ as ⊕ "\n"
      ⊕ ret ⊕ " = " ⊕ t ⊕ ";\n"

kompile-cls (absurd-clause tel ps ∷ []) ctx ret =
  -- Exactly the same as above
  -- We don't really need to make this call, but we keep it
  -- for sanity checks.  I.e. if we'll get an error in the
  -- patterns, it will bubble up to the caller.
  kompile-clpats ((tel-rename $! tel) $! []) ps ctx defaultAbsurdPatSt >>=e λ pst → do
  return $ ok "unreachable ();"

kompile-cls (absurd-clause tel ps ∷ ts@(_ ∷ _)) ctx ret =
  kompile-clpats ((tel-rename $! tel) $! []) ps ctx defaultAbsurdPatSt >>=e λ pst → do
  let (mk vars _ conds _ _) = pst
      cs = " && " ++/ (if L.length conds N.≡ᵇ 0 then [ "true" ] else conds)
  r ← kompile-cls ts ctx ret
  return $ "if (" ⊕ cs ⊕ ") {\n"
         ⊕ "unreachable();\n"
         ⊕ "} else {\n"
         ⊕ r ⊕ "\n"
         ⊕ "}\n"

kompile-cls (clause tel ps t ∷ ts@(_ ∷ _)) ctx ret =
  kompile-clpats ((tel-rename $! tel) $! []) ps ctx defaultClausePatSt >>=e λ pst → do
  let (mk vars assgns conds _ _) = pst
      cs = " && " ++/ (if L.length conds N.≡ᵇ 0 then [ "true" ] else conds)
      as = "\n" ++/ assgns
  t ← kompile-term t $! tel --telv --{!!} --PS.ctx ps
  r ← kompile-cls ts ctx ret
  return $ "if (" ⊕ cs ⊕ ") {\n"
         ⊕ as ⊕ "\n"
         ⊕ ret ⊕ " = " ⊕ t ⊕ ";\n"
         ⊕ "} else {\n"
         ⊕ r ⊕ "\n"
         ⊕ "}\n"



tel-lookup-name : Telescope → ℕ → Prog
tel-lookup-name tel n with n N.<? L.length (reverse tel)
... | yes n<l = ok $ proj₁ $ lookup (reverse tel) $ fromℕ< n<l
... | no _ = error "Variable lookup in telescope failed"

private
  kcp : String → Err PatSt
  kcp x = error $ "kompile-clpats: " ++ x

  infixl 10 _+=c_ _+=a_ _+=v_ _+=n_
  _+=c_ : PatSt → String → PatSt
  p +=c c = record p { conds = PatSt.conds p ++ [ c ] }

  _+=a_ : PatSt → String → PatSt
  p +=a a = record p { assigns = PatSt.assigns p ++ [ a ] }

  _+=v_ : PatSt → String × ℕ → PatSt
  p +=v v = record p { vars = PatSt.vars p ++ [ v ] }

  _+=n_ : PatSt → ℕ → PatSt
  p +=n n = record p { cnt = PatSt.cnt p + 1 }

  pst-fresh : PatSt → String → Err $ String × PatSt
  pst-fresh pst x =
    return $ x ++ showNat (PatSt.cnt pst) , pst +=n 1

kompile-clpats tel (arg i (con (quote true) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx $ pst +=c (v {- == true -})
kompile-clpats tel (arg i (con (quote false) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx $ pst +=c ("!" ++ v)

kompile-clpats tel (arg i (con (quote N.zero) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx $ pst +=c (v ++ " == 0")
kompile-clpats tel (arg i (con (quote N.suc) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel (ps ++ l) ((v ++ " - 1") ∷ ctx) $ pst +=c (v ++ " > 0")

kompile-clpats tel (arg i (con (quote F.zero) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx $ pst +=c (v ++ " == 0")
kompile-clpats tel (arg i (con (quote F.suc) ps@(_ ∷ _ ∷ [])) ∷ l) (v ∷ ctx) pst = do
  (ub , pst) ← pst-fresh pst "ub_"
  -- XXX here we are not using `ub` in conds.  For two reasons:
  -- 1) as we have assertions, we should check the upper bound on function entry
  -- 2) typically, the value of this argument would be Pat.dot, which we ignore
  --    right now.  It is possible to capture the value of the dot-patterns, as
  --    they carry the value when reconstructed.
  kompile-clpats tel (ps ++ l) (ub ∷ (v ++ " - 1") ∷ ctx) $ pst +=c (v ++ " > 0")

kompile-clpats tel (arg i (con (quote L.List.[]) []) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx $ pst +=c ("emptyvec_p (" ++ v ++ ")")
kompile-clpats tel (arg i (con (quote L.List._∷_) ps@(_ ∷ _ ∷ [])) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel (ps ++ l) (("hd (" ++ v ++ ")") ∷ ("tl (" ++ v ++ ")") ∷ ctx)
                 $ pst +=c ("nonemptyvec_p (" ++ v ++ ")")

-- Almost the same as List (extra parameter in cons)
kompile-clpats tel (arg i (con (quote V.Vec.[]) []) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx $ pst +=c ("emptyvec_p (" ++ v ++ ")")
kompile-clpats tel (arg i (con (quote V.Vec._∷_) ps@(_ ∷ _ ∷ _ ∷ [])) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel (ps ++ l) (("len (" ++ v ++ ") - 1") ∷ ("hd (" ++ v ++ ")") ∷ ("tl (" ++ v ++ ")") ∷ ctx)
                 $ pst +=c ("nonemptyvec_p (" ++ v ++ ")")

-- Patterns for Ix constructors
kompile-clpats tel (arg i (con (quote Ix.[]) []) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel l ctx $ pst +=c ("emptyvec_p (" ++ v ++ ")")

kompile-clpats tel (arg i (con (quote Ix._∷_) ps@(d ∷ arg _ (dot s) ∷ arg _ (dot x) ∷ finx ∷ tailix ∷ [])) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel (d ∷ finx ∷ tailix ∷ l) (("len (" ++ v ++ ") - 1") ∷ ("hd (" ++ v ++ ")") ∷ ("tl (" ++ v ++ ")") ∷ ctx)
                 $ pst +=c ("nonemptyvec_p (" ++ v ++ ")")
kompile-clpats tel (arg i (con (quote Ix._∷_) _) ∷ l) (v ∷ ctx) pst =
  kcp $ "matching on `s` and `x` in the Ix._∷_ is not supported, please rewrite the pattern"


kompile-clpats tel (arg _ (con (quote imap) (arg _ (var i) ∷ [])) ∷ l) (v ∷ ctx) pst = do
  (ub , pst) ← pst-fresh pst $ "IMAP_" ++ v ++ "_"
  -- The only thing that `x` could be is a variable, and since
  -- we don't have higher-order functions in sac, we define a local
  -- macro.  Note that we do not pass x further, to avoid assignment.
  kompile-clpats tel l ctx $ pst +=v (ub , i) +=a ("#define " ++ ub ++ "(__x) (" ++ v ++ ")[__x]")

kompile-clpats tel (arg i (con (quote imap) (arg _ (dot _) ∷ [])) ∷ l) (v ∷ ctx) pst =
  -- We simply ignore this inner function entirely.
  kompile-clpats tel l ctx $ pst

kompile-clpats tel (arg i (con (quote imap) (arg _ (absurd _) ∷ [])) ∷ l) (v ∷ ctx) pst =
  kcp "don't know how to handle absurd pattern as an argument to imap"


kompile-clpats tel (arg i (con (quote refl) ps) ∷ l) (v ∷ ctx) pst =
  -- No constraints, as there could only be a single value.
  kompile-clpats tel l ctx pst

kompile-clpats tel (arg i (con (quote _because_) ps) ∷ l) (v ∷ ctx) pst = do
  pf , pst ← pst-fresh pst $ "pf_"
  kompile-clpats tel (ps ++ l) (v ∷ pf ∷ ctx) pst
kompile-clpats tel (arg i (con (quote Reflects.ofʸ) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel (ps ++ l) ("true" ∷ ctx) pst
kompile-clpats tel (arg i (con (quote Reflects.ofⁿ) ps) ∷ l) (v ∷ ctx) pst =
  kompile-clpats tel (ps ++ l) ("false" ∷ ctx) pst

-- End of constructors here.


kompile-clpats tel (arg (arg-info _ r) (var i) ∷ l) (v ∷ vars) pst = do
  -- Note that we do not distinguish between hidden and visible variables
  s ← tel-lookup-name tel i
  let s = nnorm s
  -- If the order of variable binding doesn't match the order
  -- of the variables in the telescope, we have to consider `i` as well.
  -- This changed with https://github.com/agda/agda/issues/5075
  let pst = pst +=v (s , i)
  let pst = if does (s ≈? "_")
            then pst
            else pst +=a (s ++ " = " ++ v ++ ";")
  kompile-clpats tel l vars pst

kompile-clpats tel (arg i (dot t) ∷ l) (v ∷ vars) pst =
  -- For now we just skip dot patterns.
  kompile-clpats tel l vars pst

kompile-clpats tel (arg i (absurd _) ∷ l) (v ∷ ctx) pst =
  -- We have to carry on as the absurdity migh only occur of the
  -- combination of other argument patterns on the right.
  --ok pst
  kompile-clpats tel l ctx pst


kompile-clpats _ [] [] pst = ok pst
-- This case is for absurd clauses that may have "leftovers" such as
-- in case of the function:
--   f : ∀ n → Fin n → ℕ → ℕ
--   f 0 () {- x -}
kompile-clpats _ [] (_ ∷ _) pst@record{ absrd = true } = ok pst

kompile-clpats tel ps ctx patst = kcp $ "failed on pattern: ["
                                     ++ (", " ++/ L.map (λ where (arg _ x) → showPattern x) ps)
                                     ++ "], ctx: [" ++ (", " ++/ ctx) ++ "]"



private
  kt : String → SKS Prog
  kt x = return $ error $ "kompile-term: " ++ x

  kt-fresh : String → SKS String
  kt-fresh x = do
    ps ← R.get
    R.modify λ k → record k{ cnt = 1 + KS.cnt k }
    return $ x ++ showNat (KS.cnt ps)

var-lookup : List VarTy → ℕ → SKS Prog
var-lookup []       _       = kt "Variable lookup failed"
var-lookup (v ∈ _ ~ _ ∷ xs) zero    = return $ ok v
var-lookup (x ∷ xs) (suc n) = var-lookup xs n

vty-lookup : List VarTy → ℕ → Err (VarTy)
vty-lookup []       _       = error "Variable lookup failed"
vty-lookup (x ∷ xs) zero    = ok x
vty-lookup (x ∷ xs) (suc n) = vty-lookup xs n


mk-mask : (n : ℕ) → List $ Fin n
mk-mask zero =    []
mk-mask (suc n) = L.reverse $ go n (suc n) N.≤-refl
  where
    sa<b⇒a<b : ∀ a b → suc a N.< b → a N.< b
    sa<b⇒a<b zero    (suc b) _        = s≤s z≤n
    sa<b⇒a<b (suc a) (suc n) (s≤s pf) = s≤s $ sa<b⇒a<b a n pf

    go : (m n : ℕ) → m N.< n → List $ Fin n
    go 0       (suc _) _  = zero ∷ []
    go (suc m) n       pf = F.fromℕ< pf ∷ go m n (sa<b⇒a<b m n pf)


te-to-lvt : Telescope → List VarTy
te-to-lvt tel = L.map (λ where (v , t) → v ∈ error "?" ~ t) tel

-- TODO lift it up
SAC-funs : List (Name × String)
SAC-funs = (quote _+_ , "_add_SxS_")
         ∷ (quote _*_ , "_mul_SxS_")
         ∷ (quote primFloatPlus , "_add_SxS_")
         ∷ (quote primFloatMinus , "_sub_SxS_")
         ∷ (quote primFloatTimes , "_mul_SxS_")
         ∷ (quote primFloatDiv , "_div_SxS_")
         ∷ (quote primFloatExp , "Math::exp")
         ∷ (quote primFloatNegate , "_neg_S_")
         ∷ []


private
  module mask-tests where
    test-mk-mask₁ : mk-mask 0 ≡ []
    test-mk-mask₁ = refl

    test-mk-mask₂ : mk-mask 1 ≡ # 0 ∷ []
    test-mk-mask₂ = refl

    test-mk-mask₃ : mk-mask 2 ≡ # 0 ∷ # 1 ∷ []
    test-mk-mask₃ = refl

kompile-arglist : (n : ℕ) → List $ Arg Term → List $ Fin n → Telescope → SKS Prog
kompile-arglist n args mask varctx with L.length args N.≟ n | V.fromList args
... | yes p | vargs rewrite p = do
                 l ← mapM (λ where (arg _ x) → kompile-term x varctx)
                          $ L.map (V.lookup vargs) mask
                 return $ ok ", " ++/ l
              where open TraversableM (StateMonad KS)

... | no ¬p | _ = kt "Incorrect argument mask"

kompile-term (var x []) vars =
  return $ tel-lookup-name vars x

kompile-term (var x args@(_ ∷ _)) vars = do
  let f = tel-lookup-name vars x
      l = L.length args
  args ← kompile-arglist l args (mk-mask l) vars
  return $ f ⊕ "(" ⊕ args ⊕ ")"

kompile-term (lit l@(float _)) vars = return $ showLiteral l ⊕ "f"
kompile-term (lit l) vars = return $ ok $ showLiteral l

kompile-term (con (quote N.zero) _) _ =
  return $ ok "0"
kompile-term (con (quote N.suc) args) vars = do
  args ← kompile-arglist 1 args [ # 0 ] vars
  return $ "(1 + " ⊕ args ⊕ ")"

kompile-term (con (quote Fin.zero) _) _ =
  return $ ok "0"
kompile-term (con (quote Fin.suc) args) vars = do
  args ← kompile-arglist 2 args [ # 1 ] vars
  return $ "(1 + " ⊕ args ⊕ ")"

kompile-term (con (quote L.List.[]) (_ ∷ (arg _ ty) ∷ [])) vars = do
  -- We want to call kompile-ty, and we need a context that "should"
  -- contain vars with their types.  But, we never actually access these
  -- types in the context, we only refer to variables, therefore the
  -- following hack is justified.
  kst ← R.get
  let ctx = L.map (λ where (v , t) → v ∈ error "?" ~ t) $ vars
      (rt , ps) = kompile-ty ty false $ record defaultPS{ kst = kst; ctx = ctx }
      in-sh = sacty-shape =<< rt
  --R.put (PS.kst ps)
  return $ "empty (" ⊕ in-sh ⊕ ")" --ok "[]"

kompile-term (con (quote L.List._∷_) args) vars = do
  args ← kompile-arglist 4 args (# 2 ∷ # 3 ∷ []) vars
  return $ "cons (" ⊕ args ⊕ ")"

-- Almost the same as List
kompile-term (con (quote V.Vec.[]) (_ ∷ (arg _ ty) ∷ [])) vars = do
  kst ← R.get
  let ctx = L.map (λ where (v , t) → v ∈ error "?" ~ t) $ vars
      (rt , ps) = kompile-ty ty false $ record defaultPS{ kst = kst; ctx = ctx }
      in-sh = sacty-shape =<< rt
  R.put (PS.kst ps)
  return $ "empty (" ⊕ in-sh ⊕ ")"

kompile-term (con (quote V.Vec._∷_) args) vars = do
  args ← kompile-arglist 5 args (# 3 ∷ # 4 ∷ []) vars
  return $ "cons (" ⊕ args ⊕ ")"

-- Ix constructors
kompile-term (con (quote Ix.[]) []) vars =
  return $ ok "[]"

kompile-term (con (quote Ix._∷_) args) vars = do
  args ← kompile-arglist 5 args (# 3 ∷ # 4 ∷ []) vars
  return $ "cons (" ⊕ args ⊕ ")"


kompile-term (con (quote refl) _) _ =
  return $ ok "tt"


-- Imaps with explicit lambdas
kompile-term (con (quote Array.Base.imap) (_ ∷ arg _ ty ∷ arg _ d ∷ X@(arg _ s) ∷ arg _ (vLam x e) ∷ [])) vars = do
  kst ← R.get
  let ctx = L.map (λ where (v , t) → v ∈ error "?" ~ t) $ vars
      (rt , ps) = kompile-ty ty false $ record defaultPS{ kst = kst; ctx = ctx }
      in-sh = sacty-shape =<< rt
      bt = bt <$> rt
  R.put (PS.kst ps)
  iv ← kt-fresh "iv_"
  let iv-type = vArg (def (quote Ix) ((vArg d) ∷ vArg s ∷ []))
  s ← kompile-term s vars
  b ← kompile-term e $! vars ++ [ (iv , iv-type) ]
  return $! "with { (. <= " ⊕ iv ⊕ " <= .): " ⊕ b ⊕ "; }: genarray (" ⊕ s ⊕ ", zero_" ⊕ bt ⊕ " (" ⊕ in-sh ⊕ "))"

-- Imaps with an expression
kompile-term (con (quote Array.Base.imap) (_ ∷ arg _ ty ∷ _ ∷ arg _ s ∷ arg _ e ∷ [])) vars = do
  kst ← R.get
  let ctx = L.map (λ where (v , t) → v ∈ error "?" ~ t) $ vars
      (rt , ps) = kompile-ty ty false $ record defaultPS{ kst = kst; ctx = ctx }
      in-sh = sacty-shape =<< rt
      bt = bt <$> rt
  R.put (PS.kst ps)
  iv ← kt-fresh "iv_"
  s ← kompile-term s vars
  b ← kompile-term e $ vars
  return $ "with { (. <= " ⊕ iv ⊕ " <= .): " ⊕ b ⊕ " (" ⊕ iv ⊕ "); }: genarray (" ⊕ s ⊕ ", zero_" ⊕ bt ⊕ " (" ⊕ in-sh ⊕ "))"


kompile-term (con c _) vars  = kt $ "don't know constructor " ++ (showName c)

-- Definitions

-- From Agda.Builtin.Nat: div-helper k m n j = k + (n + m - j) div (1 + m)
kompile-term (def (quote div-helper) (arg _ k ∷ arg _ m ∷ arg _ n ∷ arg _ j ∷ [])) vars = do
  k ← kompile-term k vars
  m ← kompile-term m vars
  n ← kompile-term n vars
  j ← kompile-term j vars
  return $ k ⊕ " + _div_SxS_ ((" ⊕ n ⊕ " + " ⊕ m ⊕ " - " ⊕ j ⊕ "), 1 + " ⊕ m ⊕ ")"

kompile-term (def (quote N._≟_) (arg _ a ∷ arg _ b ∷ [])) vars = do
  a ← kompile-term a vars
  b ← kompile-term b vars
  return $ a ⊕ " == " ⊕  b

kompile-term (def (quote V._++_) args) vars = do
  args ← kompile-arglist 6 args (# 4 ∷ # 5 ∷ []) vars
  return $ "concat (" ⊕ args ⊕ ")"


kompile-term (def (quote V.tabulate) (_ ∷ arg _ ty ∷ X@(arg _ l) ∷ arg _ (vLam x e) ∷ [])) vars = do
  kst ← R.get
  let ctx = te-to-lvt vars --L.map (λ where (v , t) → v ∈ error "?" ~ t) $ TelView.tel vars
      (rt , ps) = kompile-ty ty false $ record defaultPS{ kst = kst; ctx = ctx }
      in-sh = sacty-shape =<< rt
      bt = bt <$> rt
  R.put (PS.kst ps)
  iv ← kt-fresh "iv_"
  let iv-type = vArg (def (quote Fin) (vArg l ∷ []))
  l ← kompile-term l vars
  b ← kompile-term e $ vars ++ [(iv , iv-type)]
  return $ "with { (. <= " ⊕ iv ⊕ " <= .): " ⊕ b ⊕ "; }: genarray ([" ⊕ l ⊕ "], zero_" ⊕ bt ⊕ " (" ⊕ in-sh ⊕ "))"

kompile-term (def (quote ix-tabulate) (arg _ d ∷ X ∷ arg _ (vLam x e) ∷ [])) vars = do
  iv ← kt-fresh "iv_"
  let iv-type = vArg (def (quote Fin) (vArg d ∷ []))
  d ← kompile-term d vars
  b ← kompile-term e $ vars ++ [(iv , iv-type)]
  return $ "with { (. <= " ⊕ iv ⊕ " <= .): " ⊕ b ⊕ "; }: genarray ([" ⊕ d ⊕ "], 0)"

-- Array stuff
kompile-term (def (quote sel) (_ ∷ _ ∷ _ ∷ _ ∷ arg _ a ∷ arg _ iv ∷ [])) vars = do
  a ← kompile-term a vars
  iv ← kompile-term iv vars
  return $ a ⊕ "[" ⊕ iv ⊕ "]"

kompile-term (def (quote ix-lookup) (_ ∷ _ ∷ arg _ iv ∷ arg _ el ∷ [])) vars = do
  iv ← kompile-term iv vars
  el ← kompile-term el vars
  return $ iv ⊕ "[" ⊕ el ⊕ "]"

kompile-term (def (quote V.lookup) (_ ∷ _ ∷ _ ∷ arg _ v ∷ arg _ i ∷ [])) vars = do
  v ← kompile-term v vars
  i ← kompile-term i vars
  return $ v ⊕ "[" ⊕ i ⊕ "]"

kompile-term (def (quote V.foldr) (_ ∷ _ ∷ ty₁ ∷ arg _ (vLam _ ty₂) ∷ arg _ len ∷ arg _ (hLam _ (def f args)) ∷ arg _ neut ∷ arg _ arr ∷ [])) vars = do
  let f = case list-find-el ((RN._≟ f) ∘ proj₁) SAC-funs of λ where
            (just (_ , f)) → f
            _ → nnorm $ showName f
  len ← kompile-term len vars
  neut ← kompile-term neut vars
  arr ← kompile-term arr vars
  iv ← kt-fresh "iv_"
  return $ "with { ([0] <= " ⊕ iv ⊕ " < [" ⊕ len ⊕ "]): " ⊕ arr ⊕ "[" ⊕ iv ⊕ "]; }: fold (" ⊕ f ⊕ ", " ⊕ neut ⊕ ")"


kompile-term (def (quote reduce-1d) (_ ∷ _ ∷ arg _ s ∷ arg _ (def f args) ∷ arg _ ε ∷ arg _ a ∷ [])) vars = do
  let f = case list-find-el ((RN._≟ f) ∘ proj₁) SAC-funs of λ where
            (just (_ , f)) → f
            _ → nnorm $ showName f
  ε ← kompile-term ε vars
  a ← kompile-term a vars
  s ← kompile-term s vars
  iv ← kt-fresh "iv_"
  return $ "with { ([0] <= " ⊕ iv ⊕ " < " ⊕ s ⊕ "): " ⊕ a ⊕ "[" ⊕ iv ⊕ "]; }: fold (" ⊕ f ⊕ ", " ⊕ ε ⊕ ")"

kompile-term (def (quote reduce-1d) (Xa@(arg _ X) ∷ Ya@(arg _ Y) ∷ arg _ s ∷ arg _ L@(vLam a (vLam b e)) ∷ arg _ ε ∷ arg _ arr ∷ [])) vars = do
  a ← kt-fresh "a"
  b ← kt-fresh "b"

  kst ← R.get
  let (Xs , ps) = kompile-ty X false $ record defaultPS{ kst = kst; ctx = te-to-lvt vars }
      (Ys , ps) = kompile-ty Y false $ record ps { ctx = PS.ctx ps ++ [ a ∈ Xs ~ Xa ] }
  R.put $ PS.kst ps
  t ← kompile-term e $ vars ++ (a , Xa) ∷ (b , Ya) ∷ [] -- (PS.ctx ps ++ [ b ∈ Ys ~ Ya ])

  kst ← R.get
  fname ← kt-fresh "lifted_"
  let e , ps = kompile-ctx vars $ record defaultPS{ kst = kst }
      vs     = L.map {B = String × Prog} (λ where (v ∈ τ ~ _) → (v , (sacty-to-string <$> τ))) $′ PS.ctx ps
      vs     = vs ++ ((a , (sacty-to-string <$> Xs)) ∷ (b , (sacty-to-string <$> Ys)) ∷ [])
      vs     = ok ", " ++/ L.map (λ where (v , τ) → τ ⊕ " " ⊕ v) vs
      fun    = (sacty-to-string <$> Ys) ⊕ " " ⊕ fname ⊕ "(" ⊕ vs ⊕ ") "
             ⊕ "{ return " ⊕ t ⊕ "; }"

  -- error out in case our current context was broken
  (ok _) ← return e where (error x) → return (error x)

  --R.modify $! λ k → record k{ defs = (KS.defs k ⊕_) $! fun }
  kst ← R.get
  R.put $! record kst{ defs = KS.defs kst ⊕ fun }

  let part-app = fname ⊕ "(" ⊕ ", " ++/ L.map proj₁ vars ⊕ ")"
  ε ← kompile-term ε vars
  arr ← kompile-term arr vars
  s ← kompile-term s vars
  iv ← kt-fresh "iv_"
  return $! "with { ([0] <= " ⊕ iv ⊕ " < " ⊕ s ⊕ "): " ⊕ arr ⊕ "[" ⊕ iv ⊕ "]; }: fold (" ⊕ part-app ⊕ ", " ⊕ ε ⊕ ")"

  where
    kompile-ctx : Telescope → SPS (Err ⊤)
    kompile-ctx [] = return $ ok tt
    kompile-ctx ((v , t@(arg i x)) ∷ ctx) = do
      (ok τ) ← kompile-ty x false where (error x) → return $ error x
      P.modify λ k → record k{ ctx = PS.ctx k ++ [ v ∈ ok τ ~ t ] }
      kompile-ctx ctx

-- A bunch of functions that are mapped to id in sac
-- XXX get rid of id call, only keeping for debugging purposes.
kompile-term (def (quote F.fromℕ<) args) vars = ("id (" ⊕_) ∘ (_⊕ ")") <$> kompile-arglist 3 args (# 0 ∷ []) vars
kompile-term (def (quote F.toℕ)    args) vars = ("id (" ⊕_) ∘ (_⊕ ")") <$> kompile-arglist 2 args (# 1 ∷ []) vars
kompile-term (def (quote subst-ar) args) vars = ("id (" ⊕_) ∘ (_⊕ ")") <$> kompile-arglist 7 args (# 6 ∷ []) vars
kompile-term (def (quote subst-ix) args) vars = ("id (" ⊕_) ∘ (_⊕ ")") <$> kompile-arglist 5 args (# 4 ∷ []) vars
kompile-term (def (quote ▾_)       args) vars = ("id (" ⊕_) ∘ (_⊕ ")") <$> kompile-arglist 6 args (# 5 ∷ []) vars
kompile-term (def (quote ▴_)       args) vars = ("id (" ⊕_) ∘ (_⊕ ")") <$> kompile-arglist 6 args (# 5 ∷ []) vars
kompile-term (def (quote a→ix)     args) vars = ("id (" ⊕_) ∘ (_⊕ ")") <$> kompile-arglist 4 args (# 1 ∷ []) vars
kompile-term (def (quote a→s)      args) vars = ("id (" ⊕_) ∘ (_⊕ ")") <$> kompile-arglist 2 args (# 1 ∷ []) vars


kompile-term (def (quote Array.Base.magic-fin) args) vars = return $ ok "unreachable ()"

kompile-term (def (quote Array.Base.off→idx) args) vars = do
  args ← kompile-arglist 3 args (# 1 ∷ # 2 ∷ []) vars
  return $ "off_to_idx (" ⊕ args ⊕ ")"
kompile-term (def (quote _↑_) args) vars = do
  args ← kompile-arglist 7 args (# 4 ∷ # 5 ∷ []) vars
  return $ "take (" ⊕ args ⊕ ")"
kompile-term (def (quote _↓_) args) vars = do
  args ← kompile-arglist 7 args (# 4 ∷ # 5 ∷ []) vars
  return $ "drop (" ⊕ args ⊕ ")"

kompile-term (def (quote _↑⟨_⟩_) args) vars = do
  args ← kompile-arglist 7 args (# 4 ∷ # 5 ∷ # 6 ∷ []) vars
  return $ "overtake (" ⊕ args ⊕ ")"
kompile-term (def (quote _-↑⟨_⟩_) args) vars = do
  args ← kompile-arglist 7 args (# 4 ∷ # 5 ∷ # 6 ∷ []) vars
  return $ "overtake_back (" ⊕ args ⊕ ")"

-- The last pattern in the list of `def` matches
kompile-term (def n []) _ =
  kt $ "attempting to compile `" ++ showName n ++ "` as function with 0 arguments"

kompile-term (def n args@(_ ∷ _)) vars with list-find-el ((RN._≟ n) ∘ proj₁) SAC-funs
... | just (_ , f) = do
  let l = L.length args
  args ← kompile-arglist l args (mk-mask l) vars
  return $ f ⊕ " (" ⊕ args ⊕ ")"

... | nothing  = do
  R.modify λ k → record k { funs = KS.funs k ++ [ n ] }
  let n = nnorm $ showName n
      l = L.length args
  args ← kompile-arglist l args (mk-mask l) vars
  return $ n ⊕ " (" ⊕ args ⊕ ")"

kompile-term t vctx = kt $ "failed to compile term `" ++ showTerm t ++ "`"
