module

public import GroundTheory.AutomorphicForms.SmoothRepContragredient
public import GroundTheory.AutomorphicForms.GL2.GJUnramified
public import GroundTheory.AutomorphicForms.GL2.GJStandardLUnramified
public import GroundTheory.AutomorphicForms.WhittakerCriterion
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal Parabolic

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem matrixCoeff_inv_eq_contragredient (π : Representation ℂ (GL (Fin n) F) V) (v₀ : V)
    {ℓ₀ : Module.Dual ℂ V} (hℓ₀ : ℓ₀ ∈ smoothVectors (Representation.dual π)) (g : GL (Fin n) F) :
    Parabolic.matrixCoeff π v₀ ℓ₀ g⁻¹ =
      Parabolic.matrixCoeff (contragredient π) ⟨ℓ₀, hℓ₀⟩ (evalSmooth π v₀) g :=
  rfl

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

theorem exists_satakeParameter_contragredient [NeZero n] (π : Representation ℂ (GL (Fin n) F) V)
    [π.IsIrreducible] (hπ : IsAdmissible π) (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] {v₀ : V}
    {ℓ₀ : Module.Dual ℂ V} (hℓ₀K : ℓ₀ ∈ fixedVectors (Representation.dual π) (integralGL F n))
    (hℓ₀ : ℓ₀ v₀ = 1) :
    ∃ z' : Fin n → ℂˣ, Spherical.IsSatakeParameter (contragredient π) μ z' ∧
      ∀ s : ℂ, LFunction (contragredient π) s = ∏ i, (1 - (z' i : ℂ) * qs F s)⁻¹ := by
  have hsm : ℓ₀ ∈ smoothVectors (Representation.dual π) :=
    mem_smoothVectors_of_mem_fixedVectors (isOpen_integralGL F n) hℓ₀K
  have := Whittaker.isIrreducible_contragredient hπ
  have hadm := isAdmissible_contragredient hπ
  have hfix : (⟨ℓ₀, hsm⟩ : smoothVectors (Representation.dual π)) ∈
      fixedVectors (contragredient π) (integralGL F n) :=
    mem_fixedVectors_contragredient.2 (mem_fixedVectors_dual.1 hℓ₀K)
  have hK : fixedVectors (contragredient π) (integralGL F n) ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hfix
    have h0 : ℓ₀ = 0 := congrArg Subtype.val hfix
    rw [h0, LinearMap.zero_apply] at hℓ₀
    exact zero_ne_one hℓ₀
  obtain ⟨z', hz'⟩ := Spherical.exists_satakeParameter (μ := μ) (isSmooth_contragredient π) hK
  exact ⟨z', hz', fun s ↦ LFunction_eq_prod_of_isSatakeParameter hadm hK μ hz' s⟩

theorem zetaIntegral_inv_sphericalCoeff_of_integrable' [NeZero n]
    (π : Representation ℂ (GL (Fin n) F) V) [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] {v₀ : V} {ℓ₀ : Module.Dual ℂ V}
    (hℓ₀K : ℓ₀ ∈ fixedVectors (Representation.dual π) (integralGL F n)) (hℓ₀ : ℓ₀ v₀ = 1) {s : ℂ}
    (hI : Integrable (fun g : GL (Fin n) F ↦ integralIndicator F n (g : Matrix (Fin n) (Fin n) F) *
      Parabolic.matrixCoeff π v₀ ℓ₀ g⁻¹ * detPow g (s + ((n : ℂ) - 1) / 2)) μ) :
    ∃ z' : Fin n → ℂˣ, Spherical.IsSatakeParameter (contragredient π) μ z' ∧
      (∀ i, ‖(z' i : ℂ) * qs F s‖ < 1) ∧
      (∀ t : ℂ, LFunction (contragredient π) t = ∏ i, (1 - (z' i : ℂ) * qs F t)⁻¹) ∧
      zetaIntegral μ (integralIndicator F n) (fun g ↦ Parabolic.matrixCoeff π v₀ ℓ₀ g⁻¹) s =
        (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * LFunction (contragredient π) s := by
  have hsm : ℓ₀ ∈ smoothVectors (Representation.dual π) :=
    mem_smoothVectors_of_mem_fixedVectors (isOpen_integralGL F n) hℓ₀K
  obtain ⟨z', hz', hL⟩ := exists_satakeParameter_contragredient π hπ μ hℓ₀K hℓ₀
  have hfix : (⟨ℓ₀, hsm⟩ : smoothVectors (Representation.dual π)) ∈
      fixedVectors (contragredient π) (integralGL F n) :=
    mem_fixedVectors_contragredient.2 (mem_fixedVectors_dual.1 hℓ₀K)
  have hev : evalSmooth π v₀ ⟨ℓ₀, hsm⟩ = 1 := hℓ₀
  have hfun : (fun g : GL (Fin n) F ↦ Parabolic.matrixCoeff π v₀ ℓ₀ g⁻¹) =
      Parabolic.matrixCoeff (contragredient π) ⟨ℓ₀, hsm⟩ (evalSmooth π v₀) :=
    funext (matrixCoeff_inv_eq_contragredient π v₀ hsm)
  have hI' : Integrable (fun g : GL (Fin n) F ↦ integralIndicator F n (g : Matrix (Fin n) (Fin n) F) *
      Parabolic.matrixCoeff (contragredient π) ⟨ℓ₀, hsm⟩ (evalSmooth π v₀) g *
        detPow g (s + ((n : ℂ) - 1) / 2)) μ := hI
  obtain ⟨hw, heq⟩ := zetaIntegral_sphericalCoeff_of_integrable μ hz' hfix hev hI'
  refine ⟨z', hz', hw, hL, ?_⟩
  rw [hfun, heq, hL s]

theorem zetaIntegral_inv_sphericalCoeff_of_integrable [NeZero n]
    (π : Representation ℂ (GL (Fin n) F) V) [π.IsIrreducible] (hπ : IsAdmissible π)
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] {v₀ : V} {ℓ₀ : Module.Dual ℂ V}
    (hℓ₀K : ℓ₀ ∈ fixedVectors (Representation.dual π) (integralGL F n)) (hℓ₀ : ℓ₀ v₀ = 1) {s : ℂ}
    (hI : Integrable (fun g : GL (Fin n) F ↦ integralIndicator F n (g : Matrix (Fin n) (Fin n) F) *
      Parabolic.matrixCoeff π v₀ ℓ₀ g⁻¹ * detPow g (s + ((n : ℂ) - 1) / 2)) μ) :
    zetaIntegral μ (integralIndicator F n) (fun g ↦ Parabolic.matrixCoeff π v₀ ℓ₀ g⁻¹) s =
      (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * LFunction (contragredient π) s :=
  (zetaIntegral_inv_sphericalCoeff_of_integrable' π hπ μ hℓ₀K hℓ₀ hI).choose_spec.2.2.2

end GJStandardL

end

end GroundTheory.Automorphic
