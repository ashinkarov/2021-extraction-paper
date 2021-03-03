open import Structures
open import Reflection as RE hiding (return; _>>=_; _>>_)
open import Reflection.Show

module Extract (kompile-fun : Type → Term → Name → SKS Prog) where

open import Reflection.Term
import      Reflection.Name as RN
open import Agda.Builtin.Reflection using (withReconstructed; dontReduceDefs; onlyReduceDefs)

open import Data.List as L hiding (_++_)
open import Data.Unit using (⊤)
open import Data.Product
open import Data.Bool
open import Data.String as S hiding (_++_)
open import Data.Maybe as M hiding (_>>=_)

open import Function

open import ReflHelper

open import Category.Monad using (RawMonad)
open import Category.Monad.State using (StateTMonadState; RawMonadState)
open RawMonad {{...}} public


{-# TERMINATING #-}
kompile-fold   : TCS Prog

macro
  -- Main entry point of the extractor.
  -- `n` is a starting function of the extraction
  -- `base` is the set of base functions that we never traverse into.
  -- `skip` is the list of functions that we have traversed already.
  -- The difference between the two is that `base` would be passed to
  -- `dontReduceDefs`, hence never inlined; whereas `skip` mainly avoids
  -- potential recursive extraction.
  kompile : Name → Names → Names → Term → TC ⊤
  kompile n base skip hole = do
    (p , st) ← kompile-fold $ ks [ n ] base skip ε 1
    --let p = KS.defs st ⊕ p
    q ← quoteTC p
    unify hole q


-- Traverse through the list of the functions we need to extract
-- and collect all the definitions.
kompile-fold = do
    s@(ks fs ba done _ c) ← R.get
    case fs of λ where
      []       → return ε
      (f ∷ fs) → case list-has-el (f RN.≟_) done of λ where
        true → do
          R.modify λ k → record k{ funs = fs }
          kompile-fold
        false → do
          (ty , te) ← lift-state {RM = monadTC} $ do
              ty ← getType f
              ty ← withReconstructed $ dontReduceDefs ba $ normalise ty
              te ← withReconstructed $ getDefinition f >>= λ where
                    (function cs) → return $ pat-lam cs []
                    -- FIXME: currently we do not extract data types, which
                    --        we should fix by parametrising this module by
                    --        kompile-type argument, and calling it in the
                    --        same way as we call kompile-fun now.
                    --(data-cons d) → return $ con d []
                    _ → return unknown
              te ← pat-lam-norm te ba
              return $ ty , te
          case te of λ where
            unknown →
              return $ error $ "kompile: attempting to compile `" ++ showName f ++ "` as function"
            _ → do
                R.put (ks fs ba (f ∷ done) ε c)
                -- Compile the function and make an error more specific in
                -- case compilation fails.
                (ok q) ← lift-mstate {RM = monadTC} $ kompile-fun ty te f
                  where (error x) → return $ error $ "in function " ++ showName f ++ ": " ++ x
                defs ← KS.defs <$> R.get
                let q = defs ⊕ q
                   --R.modify $! λ k → record k{ defs = ε }
                kst ← R.get
                  --let q = KS.defs kst ⊕ q
                R.put $! record kst{ defs = ε }
                -- Do the rest of the functions
                p ← kompile-fold
                return $! p ⊕ "\n\n" ⊕ q
  where
    module R = RawMonadState (StateTMonadState KS monadTC)

