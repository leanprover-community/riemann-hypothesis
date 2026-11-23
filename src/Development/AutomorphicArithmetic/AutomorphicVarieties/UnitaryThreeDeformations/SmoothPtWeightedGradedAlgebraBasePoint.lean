module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AbsDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.MemSatSqIffConstantCoeffAndLinearCoeffEqZero
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

@[expose] public section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

theorem UpperTheory.smoothPt_weightedGradedAlgebra_basePoint :
    ∀ (O : Type) [CommRing O] [IsDomain O] (σ : Type) [Fintype σ] (wt : σ → ℤ),
        SmoothPt (Fgr O wt) (x0 O wt) (fun j => Nat.card {i // wt i = j}) := by
  intro O _ _ σ hσ wt
  classical
  have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  let φ : FA O wt →ₐ[O] MvPowerSeries σ (FractionRing O) :=
    (MvPowerSeries.mapAlgHom (Algebra.ofId O (FractionRing O))).comp (WPres.free O wt).A.val
  have hφ : ∀ (f : FA O wt) (d : σ →₀ ℕ),
      coeff d (φ f) = algebraMap O (FractionRing O) (coeff d (ser f)) := fun f d => rfl
  refine ⟨σ, hσ, wt, φ, ⟨?_, ?_, ?_, ?_⟩, fun j => rfl⟩
  · intro j f hf d hd
    rw [hφ, mem_Fgr.1 hf d hd, map_zero]
  · intro f
    rw [weightedSeriesOrigin_apply]
    exact hφ f 0
  · intro i
    have hz : ser ((WPres.free O wt).zA i) = MvPowerSeries.X i := rfl
    refine ⟨(WPres.free O wt).zA i, ?_, fun i' hi => ?_⟩
    · rw [hφ, hz, coeff_index_single_self_X, map_one]
      exact one_ne_zero
    · rw [hφ, hz, coeff_index_single_X, if_neg hi, map_zero]
  · intro f h0 h1
    refine (UpperTheory.mem_satSq_iff_constantCoeff_and_linearCoeff_eq_zero O σ wt f).2 ⟨by rw [← weightedSeriesOrigin_apply, h0], fun i => hinj ?_⟩
    rw [← hφ, h1, map_zero]
