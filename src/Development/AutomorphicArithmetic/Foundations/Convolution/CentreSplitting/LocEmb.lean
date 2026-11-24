module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ClsBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.locEmb :
    UpperTheory.ConvolutionTheory.Dp.LocEmb := by
  intro E _ _ _ n μ _ π V h
  have hcar := h.carrier_eq
  have hcen : ∀ ψ : Cm.carrier π, ψ.1 ∈ centralCuspForms E n := fun ψ => (hcar.le ψ.2).1
  have hV : ∀ ψ : Cm.carrier π, clsL μ ψ.1 ∈ V := fun ψ => (hcar.le ψ.2).2
  obtain ⟨hinj, -, heq, -⟩ := UpperTheory.ConvolutionTheory.Dp.clsBasic E n μ
  obtain ⟨-, -, -, hdense⟩ := UpperTheory.ConvolutionTheory.Dp.formsIrr E n μ V h.summand
  let J0 : Cm.carrier π →ₗ[ℂ] V := ((clsL μ).comp (Cm.carrier π).subtype).codRestrict V hV
  have hJ0 : ∀ ψ, (J0 ψ).1 = clsL μ ψ.1 := fun _ => rfl
  refine ⟨J0 ∘ₗ (Cm.carrierEq π).symm.toLinearMap, ?_, ?_, ?_, ?_⟩
  · have hi : Function.Injective J0 := fun a b hab => by
      have h0 : clsL μ (a.1 - b.1) = 0 := by
        rw [map_sub, ← hJ0, ← hJ0, hab, sub_self]
      exact Subtype.ext (sub_eq_zero.1 (hinj _ (Submodule.sub_mem _ (hcen a) (hcen b)) h0))
    exact hi.comp (Cm.carrierEq π).symm.injective
  · intro v
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    have himg : (Subtype.val '' Set.range (J0 ∘ₗ (Cm.carrierEq π).symm.toLinearMap) : Set (LL μ)) =
        ((formsIn μ V).map (clsL μ) : Submodule ℂ (LL μ)) := by
      ext x
      constructor
      · rintro ⟨_, ⟨φ, rfl⟩, rfl⟩
        exact ⟨_, hcar ▸ ((Cm.carrierEq π).symm φ).2, rfl⟩
      · rintro ⟨ψ, hψ, rfl⟩
        have hψ' : ψ ∈ Cm.carrier π := hcar ▸ hψ
        refine ⟨_, ⟨Cm.carrierEq π ⟨ψ, hψ'⟩, rfl⟩, ?_⟩
        simp [hJ0]
    have hc : (v : LL μ) ∈ closure (((formsIn μ V).map (clsL μ) : Submodule ℂ (LL μ)) : Set (LL μ)) :=
      hdense.ge v.2
    rw [← himg] at hc
    exact hc
  · intro ψ
    simp [hJ0]
  · intro w g φ
    obtain ⟨ψ, rfl⟩ := (Cm.carrierEq π).surjective φ
    apply Subtype.ext
    set ψ' := (Cm.carrierEq π).symm (π.locRep w g (Cm.carrierEq π ψ)) with hψ'
    have hx : ∀ x, ψ'.1.1 x = ψ.1.1 (x * finGL E n (locGL E n w g)) := fun x => by
      have h1 : Cm.carrierEq π ψ' = π.locRep w g (Cm.carrierEq π ψ) := (Cm.carrierEq π).apply_symm_apply _
      exact congrArg (fun f : π.V => f.1.1 x) h1
    have h2 := heq ψ.1 (hcen ψ) ψ'.1 (finGL E n (locGL E n w g)) hx
    show clsL μ ψ'.1 = RG μ (finGL E n (locGL E n w g)) (clsL μ ((Cm.carrierEq π).symm (Cm.carrierEq π ψ)).1)
    rw [LinearEquiv.symm_apply_apply]
    exact h2
