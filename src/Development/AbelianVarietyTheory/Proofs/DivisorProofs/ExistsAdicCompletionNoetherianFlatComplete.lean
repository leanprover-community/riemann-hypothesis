module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
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
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.AdicPackage

theorem adicCompletion_package : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I : Ideal B),
    ∃ (C : Type) (_ : CommRing C) (φ : B →+* C), IsNoetherianRing C ∧ φ.Flat ∧
      IsAdicComplete (I.map φ) C ∧ ∀ (m : ℕ) (a : Ideal B), I ^ m ≤ a → (a.map φ).comap φ = a := by
  intro B _ _ I
  have fg : I.FG := IsNoetherian.noetherian I
  refine ⟨AdicCompletion I B, inferInstance, algebraMap B (AdicCompletion I B),
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion B I,
    RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian I),
    AdicCompletion.isAdicComplete_self I fg, ?_⟩
  intro m a h
  refine le_antisymm ?_ Ideal.le_comap_map
  have key : ∀ y : B, (AdicCompletion.evalₐ I m) (algebraMap B (AdicCompletion I B) y) =
      Ideal.Quotient.mk (I ^ m) y := fun y => (AdicCompletion.evalₐ I m).commutes y
  have hle : a.map (algebraMap B (AdicCompletion I B)) ≤
      (a.map (Ideal.Quotient.mk (I ^ m))).comap (AdicCompletion.evalₐ I m) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    simp only [Ideal.mem_comap]
    rw [key]
    exact Ideal.mem_map_of_mem _ hy
  intro x hx
  rw [Ideal.mem_comap] at hx
  have h2 := hle hx
  rw [Ideal.mem_comap, key] at h2
  exact (Ideal.mem_quotient_iff_mem h).1 h2

end GlobalTheory.AdicPackage
