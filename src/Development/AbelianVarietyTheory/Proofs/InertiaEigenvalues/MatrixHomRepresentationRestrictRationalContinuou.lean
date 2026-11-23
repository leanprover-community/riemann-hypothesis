module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KroneckerTransposeMulVec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem isRat_homRep_restrict : ∀ (l : ℕ) [Fact l.Prime] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r : ℕ) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → IsRat r (homRep (ρ₁.comp (Subgroup.inclusion (GK_le hK))) (ρ₂.comp (Subgroup.inclusion (GK_le hK)))) := by
  intro l _ a b _ _ _ _ K K' hK r ρ ρ₁ ρ₂ c hρ hb
  set ι := Subgroup.inclusion (GK_le hK) with hι
  have e1 : ∀ g i j, (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) i j = (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i) (Sum.inl j) := by
    intro g i j; rw [hb]; rfl
  have e2 : ∀ g i j, (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)) i j = (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr i) (Sum.inr j) := by
    intro g i j; rw [hb]; rfl
  have key : ∀ g' p q, ((homRep (ρ₁.comp ι) (ρ₂.comp ι) g' : GL (a × b) ↥(MaximalUnramifiedExtension l)) : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)) p q =
      (ρ (ι g') : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl p.1) (Sum.inl q.1) *
        (ρ (ι g')⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr q.2) (Sum.inr p.2) := by
    intro g' p q
    rw [homRep_apply, homUnit_val, Matrix.kroneckerMap_apply, Matrix.transpose_apply, ← map_inv, MonoidHom.comp_apply,
      MonoidHom.comp_apply, e1, e2, map_inv ι]
  have hιc : Continuous ι := continuous_subtype_val.subtype_mk _
  refine ⟨hρ.pos, fun x hx => hK (hρ.le x hx), ?_, ?_⟩
  · intro g p q
    rw [key, map_mul, hρ.rat, hρ.rat]
  · intro p q
    simp only [key, IntermediateField.coe_mul]
    exact ((hρ.cont _ _).comp hιc).mul ((hρ.cont _ _).comp (hιc.inv))

end GlobalTheory.PMon
