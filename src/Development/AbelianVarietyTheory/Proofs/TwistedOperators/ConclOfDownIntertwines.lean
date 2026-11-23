module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.DataRows
import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
public import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.KappaLevels

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]


omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ H] in
theorem inner_of_normSq (u : E →ₗ[ℂ] H) (n : ℝ) (h : ∀ x, ‖u x‖ ^ 2 = n * ‖x‖ ^ 2) (x y : E) :
    ⟪u x, u y⟫_ℂ = (n : ℂ) * ⟪x, y⟫_ℂ := by
  have h' : ∀ z, ((‖u z‖ : ℝ) : ℂ) ^ 2 = (n : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2 := fun z => by exact_mod_cast h z
  have e1 := inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (u x) (u y)
  have e2 := inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) x y
  rw [← map_smul, ← map_add (f := _), ← map_add (f := _), ← map_sub, ← map_sub] at e1
  rw [e1, e2]
  have h1 := h' (x + y)
  have h2 := h' (x - y)
  have h3 := h' (x - (RCLike.I : ℂ) • y)
  have h4 := h' (x + (RCLike.I : ℂ) • y)
  simp only [Complex.coe_algebraMap]
  rw [h1, h2, h3, h4]
  ring

theorem iota_adjoint_transport {E' H' : Type} [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (Θ : E →ₗ[ℂ] H) (ι : E' →ₗ[ℂ] H')
    (V : Submodule ℂ E') (uA : E' →ₗ[ℂ] E) (uE : H' →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n) (nA : ∀ x, ‖uA x‖ ^ 2 = n * ‖x‖ ^ 2)
    (nE : ∀ x, ‖uE x‖ ^ 2 = n * ‖x‖ ^ 2) (hι : ∀ x ∈ V, uE (ι x) = Θ (uA x)) (y : H')
    (hy : LinearMap.adjoint Θ (uE y) ∈ V.map uA) {a : ℂ} (ha : Θ (LinearMap.adjoint Θ (uE y)) = a • uE y) :
    (ι.domRestrict (V ⊓ (V ⊓ LinearMap.ker ι)ᗮ) ∘ₗ LinearMap.adjoint (ι.domRestrict (V ⊓ (V ⊓ LinearMap.ker ι)ᗮ))) y = a • y := by
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨z, hz, hzw⟩ := hy
  have key : ∀ u ∈ V, ⟪u, z⟫_ℂ = ⟪ι u, y⟫_ℂ := fun u hu => by
    apply mul_left_cancel₀ hne
    rw [← inner_of_normSq uA _ nA, ← inner_of_normSq uE _ nE, hzw, hι u hu, LinearMap.adjoint_inner_right]
  have hQ : z ∈ V ⊓ (V ⊓ LinearMap.ker ι)ᗮ := by
    refine ⟨hz, (Submodule.mem_orthogonal _ _).2 fun u hu => ?_⟩
    rw [key u hu.1, LinearMap.mem_ker.1 hu.2, inner_zero_left]
  have hb : LinearMap.adjoint (ι.domRestrict (V ⊓ (V ⊓ LinearMap.ker ι)ᗮ)) y = ⟨z, hQ⟩ := by
    refine ext_inner_left ℂ fun u => ?_
    rw [LinearMap.adjoint_inner_right, Submodule.coe_inner]
    exact (key u u.2.1).symm
  have hinj : Function.Injective uE := (injective_iff_map_eq_zero uE).2 fun y hy => by
    have := nE y
    rw [hy, norm_zero, zero_pow two_ne_zero] at this
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 this.symm).resolve_left hn.ne'))
  apply hinj
  rw [LinearMap.comp_apply, hb, map_smul, ← ha, ← hzw]
  exact hι z hz

end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

variable {R F}

end GlobalTheory.KappaLevels

end
