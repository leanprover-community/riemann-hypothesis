module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

namespace DualTopStackedExistence

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem dualLattice_mono {F F' : HermLattice K i} (h : F'.lattice ≤ F.lattice) :
    dualLattice F ≤ dualLattice F' :=
  fun _ hφ x hx => hφ x (h hx)

theorem card_eq_of_bijective {F : HermLattice K i} {T : Type} [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    Fintype.card T = Fintype.card ((K →+* ℂ) × Fin i) := by
  have h := (LinearEquiv.ofBijective (Matrix.mulVecLin (dualEmbMatrix b)) hb).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h
  exact h.symm

theorem exists_stacked {F F' : HermLattice K i} (h : F'.lattice ≤ F.lattice) {T T' : Type} [Fintype T]
    [DecidableEq T] [Fintype T'] [DecidableEq T'] (b : Module.Basis T ℤ (dualLattice F))
    (b' : Module.Basis T' ℤ (dualLattice F')) (hcard : Fintype.card T = Fintype.card T') :
    ∃ (b₁ : Module.Basis T' ℤ (dualLattice F)) (b₁' : Module.Basis T' ℤ (dualLattice F')) (a : T' → ℤ),
      ∀ t, (b₁ t : Fin i → K) = a t • (b₁' t : Fin i → K) := by
  let eN := Submodule.comapSubtypeEquivOfLe (dualLattice_mono h)
  have hrank : Module.finrank ℤ ((dualLattice F).comap (dualLattice F').subtype) =
      Module.finrank ℤ (dualLattice F') := by
    rw [eN.finrank_eq, Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b', hcard]
  obtain ⟨b₁', a, ab, hab⟩ := Submodule.exists_smith_normal_form_of_rank_eq b' hrank
  refine ⟨ab.map eN, b₁', a, fun t => ?_⟩
  have h1 := congrArg (fun x : dualLattice F' => (x : Fin i → K)) (hab t)
  simp only [Module.Basis.map_apply]
  rw [Submodule.comapSubtypeEquivOfLe_apply_coe]
  simpa using h1

end DualTopStackedExistence

def DualTopStacked.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T ℤ (dualLattice F'))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (a : T → ℤ) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II → F'.lattice ≤ F.lattice →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    II Unit (dualBlocks T) (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (∑ t, Real.log |(a t : ℝ)|) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

end

end GroundTheory.Heights₂.Heights
