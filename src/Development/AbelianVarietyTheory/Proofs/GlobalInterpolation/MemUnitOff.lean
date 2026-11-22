module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.InfiniteGroup
public import Formalism.LocalToGlobal.Columns.DecoFin

@[expose] public section

noncomputable section

namespace GlobalTheory.LvT.Inh

open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)

instance mulActPP {q : ℕ} {F : Type} [Field F] (Lc : LocF q F) (n : ℕ) : MulAction (GL (Fin n) Lc.K) (LocF.PP Lc n) where
  smul := LevModel.actPP
  one_smul p := LevModel.isAct_unique (LevModel.isAct_actPP 1 p) (fun x => by simp)
  mul_smul g h p := LevModel.isAct_unique (LevModel.isAct_actPP (g * h) p) (fun x => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    have h1 := LevModel.isAct_actPP g (LevModel.actPP h p) (Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) x)
    have h2 := LevModel.isAct_actPP h p x
    exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩)

def valO {K : Type} [Field K] [NumberField K] (Q : HeightOneSpectrum (𝓞 K)) : Subring K :=
  (Q.valuation K).valuationSubring.toSubring

theorem mem_valO {K : Type} [Field K] [NumberField K] (Q : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ valO Q ↔ Q.valuation K x ≤ 1 :=
  Iff.rfl

attribute [instance] Ar.st

end GlobalTheory.LvT.Inh
