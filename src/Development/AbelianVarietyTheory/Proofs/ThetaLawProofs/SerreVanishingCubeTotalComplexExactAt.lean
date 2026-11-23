module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsFiniteGradedModuleLineBundleSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegree
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SecCubeExactAtZeroAndOne
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory.KeyKa

theorem secCube_tw_exactAt_of_veryAmpleBy : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∀ p, (cubeComplex (secCube f (tw M H t) (fun i => Out.nonzeroLocus (s i)))).ExactAt p := by
  intro R _ _ Y f H m s M hH hM hv
  obtain ⟨N, _, _, _, _, 𝒩, _, _, hfin, hφ⟩ :=
    GlobalTheory.AbLaw.exists_finite_graded_module_secCube R Y f H m s M hH hM hv
  obtain ⟨n₀, hn⟩ := GlobalTheory.cubeComplex_grCube_exactAt_of_finite (Fin (m + 1)) R N 𝒩 hfin
  refine ⟨n₀, fun t ht p => ?_⟩
  have h01 := secCube_exactAt_zero_and_one R Y f (tw M H t) (Fin (m + 1))
    (fun i => Out.nonzeroLocus (s i)) hv.1
  match p with
  | 0 => exact h01.1
  | 1 => exact h01.2
  | p + 2 =>
    obtain ⟨φ, hb⟩ := hφ t
    have := isIso_cechComplexMap φ hb
    rw [← cechComplex_exactAt_succ_iff_cube]
    exact ((cechComplex_exactAt_succ_iff_cube _ p).2 (hn t ht (p + 2))).of_iso
      (asIso (cechComplexMap φ))

end GlobalTheory.KeyKa
