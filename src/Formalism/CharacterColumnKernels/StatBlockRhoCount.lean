module

public import Formalism.CharacterColumnKernels.StatementRho
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset

noncomputable section

namespace Formalism.NG

def StatBlockRhoAbs : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (G : Type*) [Group G]
    (d : Type) [Fintype d] (ρM : Representation O G (d → KO O)) (H : Type*) [AddCommGroup H]
    [Module O H] (Ψ : H →ₗ[O] coZ1s ρM) (δ : O),
    (∀ h : H, ∀ v : d → KO O, (Ψ h : G → (d → KO O)) = coD0 ρM v → (δ * δ) • v = 0) →
    ∀ (ι : Type*) [DecidableEq ι] (what₂ cols : Finset ι) (D : ι → Subgroup G)
      (F : ∀ w, Submodule O (H1z (resRep ρM (D w))))
      (lenRow : ι → ℕ∞) (Q : Submodule O (H1z ρM)) (s : ℕ∞) (ℓ : ℕ) (e' j : ι → ℕ) (h0 : ι → ℕ∞),
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δ
    let N : ℕ∞ := Fintype.card d
    (∀ w ∈ what₂, ∃ A : Submodule O (H1z (resRep ρM (D w))), F w ≤ A ∧
      Module.length O (A ⧸ (F w).comap A.subtype) ≤ lenRow w ∧
      ∀ h : H, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ A) →
    (∀ w ∈ cols, ∀ h : H, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h : H, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ s →
    Module.length O (LinearMap.ker Ψ) ≤
      ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + (cols.card : ℕ∞) * N * vδ →
    Module.length O H ≤
      ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + s +
        4 * N * ((cols.card : ℕ∞) + 1) * vδ

abbrev ColData (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : ℕ) (δ : O)
    (e' j : ℕ) (Xw : Type*) [AddCommGroup Xw] [Module O Xw] (d : Type) [Fintype d] : Type _ :=
  (Fin j → LinearMap.ker (DistribSMul.toLinearMap O (KO O) ((ℓ : O) ^ e' * δ))) × Xw ×
    LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δ)

end Formalism.NG
