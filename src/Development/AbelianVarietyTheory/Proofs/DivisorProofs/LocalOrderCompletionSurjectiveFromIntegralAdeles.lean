module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MulMemIntA
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.OrdLift

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_mem_intAf : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F := fun v => by
  rw [map_one]; exact one_mem _

theorem mul_mem_intA {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E} (hx : x ∈ GlobalTheory.PlaceComp.intA F E)
    (hy : y ∈ GlobalTheory.PlaceComp.intA F E) : x * y ∈ GlobalTheory.PlaceComp.intA F E :=
  by apply _root_.UpperTheory.Reformulated.B.Uc13.mul_mem_intA <;> assumption

end GlobalTheory.OrdLift

theorem GlobalTheory.OrdLift.ordAt_lift : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E),
    a ∈ GlobalTheory.PlaceComp.ordAt E v → ∃ t ∈ GlobalTheory.PlaceComp.intA F E, GlobalTheory.PlaceComp.evF E v t = a := by
  intro F E _ _ _ _ _ v a ha
  induction ha using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, x, rfl⟩ := hy
    refine ⟨Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v b ⊗ₜ[F] (x : E),
      AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf F v ⟨b, hb⟩, x, rfl⟩, ?_⟩
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v b) ⊗ₜ[F] (x : E) = _
    rw [GlobalTheory.SplitIdem.evalV_singleV_same]
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | one =>
    refine ⟨1, AddSubgroup.subset_closure ⟨1, GlobalTheory.OrdLift.one_mem_intAf F, 1, ?_⟩, map_one _⟩
    simp [Algebra.TensorProduct.one_def]
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨s + t, add_mem hs ht, map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact ⟨-s, neg_mem hs, map_neg _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨s * t, GlobalTheory.OrdLift.mul_mem_intA F E hs ht, map_mul _ _ _⟩

end
