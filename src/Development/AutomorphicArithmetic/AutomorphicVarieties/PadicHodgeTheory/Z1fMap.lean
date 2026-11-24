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

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.z1fMap :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (φ : G →* GQ l) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {A' : Type} [CommRing A'] [Algebra ℚ_[l] A'] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A' V'] (ρ : Representation A G V) (ρ' : Representation A' G V'), (ContAction ρ → ReciprocityTheory.Gal.B1 ρ ≤ UpperTheory.V.Loc.finiteCocycles φ ρ) ∧ ∀ f : V →ₗ[ℚ_[l]] V', (∀ g x, f (ρ g x) = ρ' g (f x)) → ∀ c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ, (fun g => f (c g)) ∈ UpperTheory.V.Loc.finiteCocycles φ ρ' := by
  intro l _ G _ _ φ A _ _ A' _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ ρ ρ'
  refine ⟨fun hρ => ?_, fun f hf c hc => ?_⟩
  · rintro _ ⟨v, rfl⟩
    refine ⟨⟨?_, fun g h => ?_⟩, v ⊗ₜ[ℚ_[l]] (1 : Bcr l), fun g => ?_⟩
    · have h1 : Continuous fun g : G => ρ g v :=
        Continuous.comp (g := fun p : G × V => ρ p.1 p.2) (f := fun g : G => (g, v)) hρ (by fun_prop)
      exact h1.sub continuous_const
    · simp [ReciprocityTheory.Gal.d0]
    · simp [ReciprocityTheory.Gal.d0, actC, sub_tmul]
  · obtain ⟨⟨hc, hcc⟩, x, hx⟩ := hc
    have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap f
    refine ⟨⟨hfc.comp hc, fun g h => ?_⟩, LinearMap.rTensor (Bcr l) f x, fun g => ?_⟩
    · simp only [hcc g h, map_add (f := _), hf]
    · have key : ∀ y : V ⊗[ℚ_[l]] Bcr l, LinearMap.rTensor (Bcr l) f (actC φ ρ g y) =
          actC φ ρ' g (LinearMap.rTensor (Bcr l) f y) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [actC, hf]
        | add a b ha hb => simp only [map_add (f := _), ha, hb]
      rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
