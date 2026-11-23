module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieCorrOfPowEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiePairingCanonicalRigidifiedExtensionTangent
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

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup

theorem eq_zero_of_forall_apply_psi_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → LieExact A →
    ∀ (G : PDivGroup p R) (t : TorsionTower G A) (ψ : PrimitiveSubmodule A →ₗ[R] G.omega),
    (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
    ∀ x : G.Lie, (∀ c, x (ψ c) = 0) → x = 0 := by
  intro p _ R _ N hN A _ hA hL G t ψ hψ x hx
  have : IsAdicComplete (Ideal.span {(p : R)}) R :=
    GlobalTheory.isAdicComplete_span_natCast_of_isNilpotent p R ⟨N, hN⟩
  obtain ⟨v, hv⟩ := exists_lieCorr_of_pow_eq_zero p R N hN A G t x
  obtain ⟨h, hh⟩ := hL.2 v hv.1

  have hFil : h ∈ Fil A := by
    rw [mem_Fil]
    intro f hf
    have hF : (⟨_, hf⟩ : primDR A) ∈ PrimitiveSubmodule A := by
      change Form.cl _ f ∈ F1 (A.hom ≫ 𝟙 _)
      rw [hodgeFiltration_eq_range]
      exact LinearMap.mem_range_self _ f
    rw [hh.2 f hf, ← lie_psi_cl_eq_tanVal p R N hN A hA G t ψ hψ f hf hF x v hv]
    exact hx _

  have hv1 : v = 1 := (hL.1 h).unique hh (isLieImage_one_iff.mpr hFil)
  subst hv1
  exact hv.unique_left TorsionTower.lieCorr_zero

end GlobalTheory.PDivGroup
