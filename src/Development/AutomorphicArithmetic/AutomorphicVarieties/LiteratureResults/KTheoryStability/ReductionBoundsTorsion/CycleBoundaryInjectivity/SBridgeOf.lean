module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CycleBoundaryInjectivity.ICyclesInjective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CycleBoundaryInjectivity.ThEqZeroIff
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CycleBoundaryInjectivity.Chains

@[expose] public section

noncomputable section

open UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB

open NaturalTheta in
theorem sBridge_of : SBridge := by
  intro k
  have h0 : ∀ (G : Type) [Group G] (m : ℕ),
      bd G m ∘ₗ (eC G (m + 1)).toLinearMap = (eC G m).toLinearMap ∘ₗ (Dz G m).baseChange ℝ :=
    fun G _ m => by rw [Dz_eq_bdZ]; exact bd_eC G m
  refine ⟨fun G _ => th (Dz G k) (pz G k) (eC G (k + 1)) (eC G k) (bd G k) (h0 G k), ?_, ?_, ?_⟩
  · intro G _
    exact th_surjective _ _ _ _ _ (pz_surjective G k) _
  · intro G _ z
    exact th_eq_zero_iff (Dz G (k + 1)) (Dz G k) (pz G k) (eC G (k + 2)) (eC G (k + 1)) (eC G k)
      (bd G (k + 1)) (bd G k) (Dz_Dz G k) (pz_eq_zero_iff G k) (pz_surjective G k) (h0 G (k + 1))
      (h0 G k) z
  · intro G H _ _ f z z' hz
    exact th_natural _ _ _ _ _ _ _ _ _ _ (h0 G k) (h0 H k) _ _ _ (cmap_eC G f (k + 1))
      (map_mem_ker k f) (pz_natural k f) z z' hz

end PositivityTheory.KB
