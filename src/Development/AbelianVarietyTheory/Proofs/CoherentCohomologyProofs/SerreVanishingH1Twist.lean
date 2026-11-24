module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsFiniteGradedModuleLineBundleSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegree
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FirstCohomologyVanishesOfExactSecCube
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
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem exists_h1Zero_tw_of_veryAmpleBy (R : Type) [CommRing R] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB Y) (m : ℕ)
    (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hH : H.IsLB) (hM : M.IsLB)
    (hs : VeryAmpleBy f H s) : ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → FirstCohomologyVanishes (tw M H t) := by
  obtain ⟨N, _, _, _, _, 𝒩, _, _, hN, hφ⟩ := GlobalTheory.T.exists_finite_gradedModule_lineBundleSections R Y f H m s M hH hM hs
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.cubeComplex_grCube_exactAt_of_finite (Fin (m + 1)) R N 𝒩 hN
  refine ⟨t₀, fun t ht => ?_⟩
  obtain ⟨φ, hφ⟩ := hφ t
  have := isIso_cechComplexMap φ hφ
  have h1 := (cechComplex_exactAt_succ_iff_cube _ 0).2 (ht₀ t ht 2)
  have h2 := h1.of_iso (asIso (cechComplexMap φ))
  exact firstCohomologyVanishes_of_exact_secCube R Y f (tw M H t) (Fin (m + 1)) (fun i => nonzeroLocus (s i))
    (isLB_tw hM hH t) hs.1 (fun i => (hs.2 i).1) ((cechComplex_exactAt_succ_iff _ 0).1 h2)

end GlobalTheory.AbLaw
