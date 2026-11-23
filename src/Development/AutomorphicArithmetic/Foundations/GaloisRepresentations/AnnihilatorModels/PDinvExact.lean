module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private lemma UpperTheory.Gal.crystallineComparison.map_id_eq_rTensor {F B L U V : Type} [Field F] [AddCommGroup B] [Module F B]
    [Field L] [Algebra F L] [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] (f : U →ₗ[L] V) (x : U ⊗[F] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B) x = LinearMap.rTensor B (f.restrictScalars F) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private lemma UpperTheory.Gal.crystallineComparison.inter_map {F G B L U V : Type} [Field F] [Group G] [AddCommGroup B] [Module F B]
    (σ : G → End F B) [Field L] [Algebra F L] [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    {ρ : Representation L G U} {ρ' : Representation L G V} {f : U →ₗ[L] V} (hf : Inter ρ ρ' f) (g : G) (x : U ⊗[F] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B) (AlgebraTensorModule.map (ρ g) (σ g) x) =
      AlgebraTensorModule.map (ρ' g) (σ g) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u b => simp [hf g u]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem UpperTheory.Gal.crystallineComparison.dinvExact_of :
    DinvExact := by
  intro F G B _ _ _ _ σ L _ _ U V W _ _ _ _ _ _ _ _ _ _ _ _ ρU ρV ρW i p hi hp hinj hex hfin
  have hI : Function.Injective (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B)) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := B) (i.restrictScalars F) hinj
    intro x y hxy
    apply h
    rw [← map_id_eq_rTensor, ← map_id_eq_rTensor]
    exact hxy
  have hE : Function.Exact (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B))
      (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) := by
    have h := Module.Flat.rTensor_exact (f := i.restrictScalars F) (g := p.restrictScalars F) B hex
    have e1 : (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B) : U ⊗[F] B → V ⊗[F] B) =
        LinearMap.rTensor B (i.restrictScalars F) := funext (map_id_eq_rTensor i)
    have e2 : (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) : V ⊗[F] B → W ⊗[F] B) =
        LinearMap.rTensor B (p.restrictScalars F) := funext (map_id_eq_rTensor p)
    rw [e1, e2]
    exact h
  have key : (Dinv σ ρU).map (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B)) =
      Dinv σ ρV ⊓ LinearMap.ker (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · refine (mem_Dinv σ).2 fun g => ?_
        rw [← inter_map σ hi, (mem_Dinv σ).1 hx g]
      · exact (hE _).2 ⟨x, rfl⟩
    · rintro ⟨hy, hk⟩
      obtain ⟨x, rfl⟩ := (hE y).1 hk
      refine ⟨x, (mem_Dinv σ).2 fun g => hI ?_, rfl⟩
      rw [inter_map σ hi, (mem_Dinv σ).1 hy g]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine (mem_Dinv σ).2 fun g => ?_
    rw [← inter_map σ hp, (mem_Dinv σ).1 hx g]
  · have h1 := LinearMap.finrank_range_add_finrank_ker
      ((AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)).domRestrict (Dinv σ ρV))
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h1
    have h2 : finrank L (Submodule.comap (Dinv σ ρV).subtype
        (LinearMap.ker (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)))) =
        finrank L (Dinv σ ρU) := by
      rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, ← key]
      exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hI _)).symm
    rw [h2] at h1
    omega
