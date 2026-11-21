import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.StatementsGluing
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.LocallyFreeSpreadHyp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

section Rings

variable {Ω : Type} [Field Ω]





end Rings

section Join

variable {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type}



theorem addBlockPullback_of_chartBundlePullback (h : ChartBundlePullback.Statement) :
    IndefiniteRowSideFullHecke.Antisym.AddBlockPullback.Statement := by
  intro Ω Ω' _ _ _ _ ι κ _ _ x z r E _ _ B
  exact h Ω Ω' ι κ x z r E B

end Join

section AddBlock

variable {K : Type} {ι : K → Type} {κ : Type}

def addBlockToSum : Option K → K ⊕ Unit
  | none => Sum.inr ()
  | some k => Sum.inl k

def addBlockIdxToSigma :
    (Σ o, addBlockIdx ι κ o) → (Σ k : K ⊕ Unit, Sum.elim ι (fun _ : Unit => κ) k)
  | ⟨none, i⟩ => ⟨Sum.inr (), i⟩
  | ⟨some k, i⟩ => ⟨Sum.inl k, i⟩

def sigmaToAddBlockIdx :
    (Σ k : K ⊕ Unit, Sum.elim ι (fun _ : Unit => κ) k) → (Σ o, addBlockIdx ι κ o)
  | ⟨Sum.inr (), i⟩ => ⟨none, i⟩
  | ⟨Sum.inl k, i⟩ => ⟨some k, i⟩

def addBlockIdxEquiv :
    (Σ o, addBlockIdx ι κ o) ≃ (Σ k : K ⊕ Unit, Sum.elim ι (fun _ : Unit => κ) k) where
  toFun := addBlockIdxToSigma
  invFun := sigmaToAddBlockIdx
  left_inv := by rintro ⟨_ | k, i⟩ <;> rfl
  right_inv := by rintro ⟨k | ⟨⟩, i⟩ <;> rfl




end AddBlock

section Readings

open IndefiniteRowSideFullHecke.Antisym

def ratsInReal : Subfield ℝ := (Rat.castHom ℝ).fieldRange

abbrev chartOne : Subalgebra ℤ ℝ := chartRing ℤ (fun _ : Unit => (1 : ℝ)) ()



abbrev zTwo : Subring ℝ := locAtIntPrime 2 chartOne.toSubring



def sqrtTwoLattice : Submodule zTwo ℝ := Submodule.span zTwo (Set.range ![(1 : ℝ), √2])






end Readings

end GroundTheory.Heights₂.Heights
