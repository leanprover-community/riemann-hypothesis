module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

theorem UpperTheory.V.Loc.z1fCoef :
    ∀ {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] (φ : H →* GQ l) {A A' V V' : Type} [CommRing A] [Algebra ℚ_[l] A] [CommRing A'] [Algebra ℚ_[l] A'] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V'] [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A' V'] (ρ : Representation A H V) (ρ' : Representation A' H V') (f : V →ₗ[ℚ_[l]] V'), Continuous f → (∀ g x, f (ρ g x) = ρ' g (f x)) → ∀ c ∈ finiteCocycles φ ρ, (fun g => f (c g)) ∈ finiteCocycles φ ρ' := by
  intro l _ H _ _ φ A A' V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ ρ' f hfc hf c hc
  obtain ⟨⟨hc, hcc⟩, x, hx⟩ := hc
  refine ⟨⟨hfc.comp hc, fun g h => ?_⟩, LinearMap.rTensor (Bcr l) f x, fun g => ?_⟩
  · simp only [hcc g h, map_add (f := _), hf]
  · have key : ∀ y : TensorProduct ℚ_[l] V (Bcr l), LinearMap.rTensor (Bcr l) f (actC φ ρ g y) =
        actC φ ρ' g (LinearMap.rTensor (Bcr l) f y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [actC, hf]
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
