module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechLeray
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PullCochMemCoboundaries
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace CrystallineSemistableComparison.Om.Nt2

open CrystallineSemistableComparison.Om.Glob CrystallineSemistableComparison.Om.Cech

theorem cov_aff {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (U : Pb.Cov q)
    (n : ℕ) (i : Fin (n + 1) → U.ι) : IsAffineOpen (⨅ a, U.U (i a)) := by
  classical
  have h := U.inter (Finset.univ.image i) ⟨i 0, Finset.mem_image_of_mem i (Finset.mem_univ 0)⟩
  have e : (⨅ α ∈ Finset.univ.image i, U.U α) = ⨅ a, U.U (i a) := by
    refine le_antisymm (le_iInf fun a => iInf₂_le (i a) (Finset.mem_image_of_mem i (Finset.mem_univ a))) ?_
    refine le_iInf₂ fun α hα => ?_
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
    exact iInf_le (fun a => U.U (i a)) a
  rw [e] at h
  exact h

theorem cls_eq {X : TopCat.{0}} {P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} {ι : Type}
    {U : ι → TopologicalSpace.Opens X} {n : ℕ} {σ σ' : GroundTheory.Arith.SchemeCoh.Cochain P U n} (e : σ = σ')
    (h : GroundTheory.Arith.SchemeCoh.d P U n σ = 0) (h' : GroundTheory.Arith.SchemeCoh.d P U n σ' = 0) :
    GroundTheory.Arith.SchemeCoh.cls σ h = GroundTheory.Arith.SchemeCoh.cls σ' h' := by
  subst e
  rfl

theorem capO_pre {X Y : Scheme.{0}} (u : X ⟶ Y) {ι κ : Type} (U : ι → X.Opens) (W : κ → Y.Opens) (τ : ι → κ)
    (hτ : ∀ α, U α ≤ u ⁻¹ᵁ W (τ α)) {n : ℕ} (i : Fin n → ι) : Pb.capO U i ≤ u ⁻¹ᵁ Pb.capO W (τ ∘ i) := by
  intro x hx
  rw [← SetLike.mem_coe, Pb.capO, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter] at hx
  change u.base x ∈ Pb.capO W (τ ∘ i)
  rw [← SetLike.mem_coe, Pb.capO, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  exact fun k => hτ (i k) (hx k)

def covX {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] [IsProper q] : Pb.Cov q :=
  Classical.choice ((Pb.cov_ex q).1 inferInstance)

end CrystallineSemistableComparison.Om.Nt2
