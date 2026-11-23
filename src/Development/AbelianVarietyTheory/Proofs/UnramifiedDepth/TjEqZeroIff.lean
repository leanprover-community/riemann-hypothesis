module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.TopLimitModules.LimJMemSmulTop
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TopLeAlgOverHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AddCurve
open ReciprocityTheory.ChartRestriction.G.Pdiv.TL

namespace GlobalTheory.JetExpansion

variable {k : Type} [CommRing k] {κ : Type} [Finite κ]

def tj (m : ℕ) : MvPowerSeries κ k →ₐ[k] JetR k κ m :=
  (MvPowerSeries.truncTotalAlgHom κ k (m + 1)).restrictScalars k

theorem tj_eq_iff (m : ℕ) (f g : MvPowerSeries κ k) :
    tj m f = tj m g ↔ ∀ x : κ →₀ ℕ, x.degree < m + 1 → MvPowerSeries.coeff x f = MvPowerSeries.coeff x g :=
  limJ_tt_eq_iff m f g

theorem tj_ext {f g : MvPowerSeries κ k} (h : ∀ m, tj m f = tj m g) : f = g := by
  ext x
  exact (tj_eq_iff x.degree f g).1 (h _) x (Nat.lt_succ_self _)

theorem tj_eq_zero_iff (m : ℕ) (f : MvPowerSeries κ k) :
    tj m f = 0 ↔ f ∈ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ k)) ^ (m + 1) := by
  rw [← GlobalTheory.germIdeal_eq_span, GlobalTheory.mem_germIdeal_pow_iff, ← map_zero (tj (k := k) (κ := κ) m), tj_eq_iff]
  simp only [map_zero]

theorem exists_tj (p : ∀ m, JetR k κ m) (hp : ∀ m, jetTruncR k κ m (p (m + 1)) = p m) :
    ∃ f : MvPowerSeries κ k, ∀ m, tj m f = p m := by
  choose P hP using fun m => Ideal.Quotient.mk_surjective (p m)
  have hck : ∀ (u : κ →₀ ℕ) m, u.degree ≤ m → (P m).coeff u = (P u.degree).coeff u := by
    intro u m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      rw [← ih]
      have h1 : (Ideal.Quotient.mk _ (P m) : JetR k κ m) = Ideal.Quotient.mk _ (P (m + 1)) := by
        rw [hP, ← hp m, ← hP]
        rfl
      exact ((limJ_mk_eq_iff m _ _).1 h1 u (by omega)).symm
  refine ⟨fun u => (P u.degree).coeff u, fun m => ?_⟩
  rw [← hP m]
  refine (limJ_mk_eq_iff m (MvPowerSeries.truncTotal (m + 1) _) _).2 fun u hu => ?_
  exact (MvPowerSeries.coeff_truncTotal _ hu).trans (hck u m (by omega)).symm

end GlobalTheory.JetExpansion
