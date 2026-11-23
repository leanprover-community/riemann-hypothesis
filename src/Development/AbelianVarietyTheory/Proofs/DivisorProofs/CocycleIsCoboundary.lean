module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Mathlib.Algebra.WithConv
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmitsurCohomologyH1

noncomputable def d0 (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D'] :
    D' →ₗ[D] D' ⊗[D] D' :=
  TensorProduct.mk D D' D' 1 - (TensorProduct.mk D D' D').flip 1

theorem amitsur_d0_apply (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D'] (a : D') :
    d0 D D' a = (1 : D') ⊗ₜ[D] a - a ⊗ₜ[D] (1 : D') := by
  simp [d0]

theorem cocycle_is_coboundary : ∀ (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D']
    [Module.FaithfullyFlat D D'] (c : D' ⊗[D] D'),
    (∀ (E : Type) [CommRing E] [Algebra D E] (f₁ f₂ f₃ : D' →ₐ[D] E),
      Algebra.TensorProduct.lift f₁ f₃ (fun _ _ ↦ Commute.all _ _) c =
        Algebra.TensorProduct.lift f₁ f₂ (fun _ _ ↦ Commute.all _ _) c +
          Algebra.TensorProduct.lift f₂ f₃ (fun _ _ ↦ Commute.all _ _) c) →
    ∃ a : D', c = (1 : D') ⊗ₜ[D] a - a ⊗ₜ[D] (1 : D') := by
  intro D D' _ _ _ _ c hc
  let i1 : D' →ₐ[D] D' ⊗[D] (D' ⊗[D] D') := Algebra.TensorProduct.includeLeft
  let i2 : D' →ₐ[D] D' ⊗[D] (D' ⊗[D] D') :=
    (Algebra.TensorProduct.includeRight).comp Algebra.TensorProduct.includeLeft
  let i3 : D' →ₐ[D] D' ⊗[D] (D' ⊗[D] D') :=
    (Algebra.TensorProduct.includeRight).comp Algebra.TensorProduct.includeRight
  have h := hc (D' ⊗[D] (D' ⊗[D] D')) i1 i2 i3
  have k1 : ∀ x : D' ⊗[D] D',
      Algebra.TensorProduct.lift i1 i3 (fun _ _ ↦ Commute.all _ _) x -
        Algebra.TensorProduct.lift i1 i2 (fun _ _ ↦ Commute.all _ _) x =
        LinearMap.lTensor D' (d0 D D') x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      simp [i1, i2, i3, amitsur_d0_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), ← hx, ← hy]; abel
  have k2 : ∀ x : D' ⊗[D] D',
      Algebra.TensorProduct.lift i2 i3 (fun _ _ ↦ Commute.all _ _) x = (1 : D') ⊗ₜ[D] x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      simp [i2, i3, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      rw [map_add (f := _), hx, hy, TensorProduct.tmul_add]
  have key : (1 : D') ⊗ₜ[D] c = LinearMap.lTensor D' (d0 D D') c := by
    rw [← k1, ← k2, h]; abel
  let q := (LinearMap.range (d0 D D')).mkQ
  have hq : (1 : D') ⊗ₜ[D] q c = 0 := by
    have : (1 : D') ⊗ₜ[D] q c = LinearMap.lTensor D' q ((1 : D') ⊗ₜ[D] c) := by simp
    rw [this, key, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have hz : q ∘ₗ d0 D D' = 0 := by
      ext a; simp [q]
    rw [hz]; simp
  have hq0 : q c = 0 := (Module.FaithfullyFlat.one_tmul_eq_zero_iff D _ (A := D') _).1 hq
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hq0
  exact ⟨a, by rw [← ha, amitsur_d0_apply]⟩

end GlobalTheory.AmitsurCohomologyH1
