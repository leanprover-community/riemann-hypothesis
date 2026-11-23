module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem mem_pow_smul_of_coord_dvd : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (x : ↥T.L.T) (k : ℕ), (∀ φ : ↥T.L.T →+ ℤ_[l], (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → (l : ℤ_[l]) ^ k ∣ φ x) → ∃ y ∈ T.L.T, (x : T.V) = ((l : O) ^ k) • y := by
  intro l _ O K _ _ _ _ _ _ _ _ G _ _ T x k h
  haveI : Module.Free O ↥T.L.T := T.L.free
  let b := Module.Free.chooseBasis O ↥T.L.T
  let f := Module.Free.chooseBasis ℤ_[l] O
  have hφ : ∀ i j, (l : ℤ_[l]) ^ k ∣ f.repr (b.repr x i) j := by
    intro i j
    let φ : ↥T.L.T →+ ℤ_[l] := ((f.coord j).toAddMonoidHom).comp (b.coord i).toAddMonoidHom
    have := h φ (by
      intro z t
      show f.coord j (b.coord i (algebraMap ℤ_[l] O z • t)) = z * f.coord j (b.coord i t)
      rw [LinearMap.map_smul, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul])
    simpa [φ] using this
  choose w hw using hφ
  let c : _ → O := fun i => ∑ j ∈ (f.repr (b.repr x i)).support, w i j • f j
  let y : ↥T.L.T := ∑ i ∈ (b.repr x).support, c i • b i
  have hc : ∀ i, (l : O) ^ k * c i = b.repr x i := by
    intro i
    have hl : (l : O) ^ k = algebraMap ℤ_[l] O ((l : ℤ_[l]) ^ k) := by simp
    conv_rhs => rw [← f.linearCombination_repr (b.repr x i)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hl, ← Algebra.smul_def, smul_smul, hw i j]
  have hx : x = (l : O) ^ k • y := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hc i]
  refine ⟨(y : T.V), y.2, ?_⟩
  rw [hx]
  rfl

end GlobalTheory.InertiaEigenvalues
