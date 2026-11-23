module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArithmeticHeightTower.TowerCopy

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.VdmRec GlobalTheory.ProjVar

theorem topSelf_eq_finrank_mul {X : Scheme.{0}} (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra K Γ(X, ⊤)]
    [Algebra k Γ(X, ⊤)] (hk : ∀ a : k, algebraMap k Γ(X, ⊤) a = algebraMap K Γ(X, ⊤) (algebraMap k K a))
    (M : LB X) (d : ℕ) : topSelfIntersection k M d = (Module.finrank k K : ℤ) * topSelfIntersection K M d := by
  have hχ (F : X.Modules) : chi k F = (Module.finrank k K : ℤ) * chi K F := by
    have hT (n : ℕ) : IsScalarTower k K (coh F n) := by
      refine ⟨fun a b x => ?_⟩
      change cohOn.action F ⊤ n (algebraMap K Γ(X, ⊤) (a • b)) x =
        cohOn.action F ⊤ n (algebraMap k Γ(X, ⊤) a) (cohOn.action F ⊤ n (algebraMap K Γ(X, ⊤) b) x)
      rw [Algebra.smul_def, map_mul, map_mul, hk]
      rfl
    have e (n : ℕ) : ((-1 : ℤ) ^ n * hdim k F n) = (Module.finrank k K : ℤ) * ((-1 : ℤ) ^ n * hdim K F n) := by
      rw [hdim_def, hdim_def, ← Module.finrank_mul_finrank k K (coh F n)]
      push_cast
      ring
    rw [chi_def, chi_def]
    simp_rw [e]
    exact (mul_finsum _ _).symm
  rw [topSelf_def, topSelf_def, interNum_def, interNum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [hχ]
  ring

end GlobalTheory.ArithmeticHeightTower.TowerCopy
