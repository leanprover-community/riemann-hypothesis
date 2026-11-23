module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsFiniteGradedModuleLineBundleSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteGrCechHomology
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
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem finite_cechLB_homology (R : Type) [CommRing R] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB Y) (m : ℕ)
    (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hH : H.IsLB) (hM : M.IsLB) (hv : VeryAmpleBy f H s)
    (p : ℕ) : Module.Finite R ((cechLB f M (fun i => nonzeroLocus (s i))).homology p) := by
  obtain ⟨N, _, _, _, _, 𝒩, _, _, hN, hφ⟩ :=
    exists_finite_graded_module_secCube R Y f H m s M hH hM hv
  obtain ⟨φ, hφ⟩ := hφ 0
  have := finite_grCech_homology (Fin (m + 1)) R N 𝒩 hN 0 p
  have : IsIso (cechComplexMap φ) := isIso_cechComplexMap φ hφ
  let e : cechComplex (grCube (Fin (m + 1)) 𝒩 0) ≅ cechLB f M (fun i => nonzeroLocus (s i)) :=
    asIso (cechComplexMap φ) ≪≫ (cechLBTwZero f _ hM hH).symm
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso e p).toLinearEquiv

end GlobalTheory.AbLaw
