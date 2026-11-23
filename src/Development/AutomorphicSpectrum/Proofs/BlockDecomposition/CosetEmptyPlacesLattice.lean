module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetOff
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi

private theorem forall_locMem_iff_exists_mem_ideal {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F))
    (z : F) :
    (∀ v : HeightOneSpectrum (𝓞 F), GlobalTheory.CompanionTheory.Equi.LocMem I v z) ↔ ∃ y ∈ I, (y : F) = z := by
  constructor
  · intro h
    let J : Ideal (𝓞 F) :=
      { carrier := {s | ∃ y ∈ I, (s : F) * z = y}
        add_mem' := by
          rintro a b ⟨y₁, hy₁, h₁⟩ ⟨y₂, hy₂, h₂⟩
          exact ⟨y₁ + y₂, I.add_mem hy₁ hy₂, by push_cast; rw [add_mul, h₁, h₂]⟩
        zero_mem' := ⟨0, I.zero_mem, by simp⟩
        smul_mem' := by
          rintro c a ⟨y, hy, h₁⟩
          exact ⟨c * y, I.mul_mem_left c hy, by rw [smul_eq_mul]; push_cast; rw [mul_assoc, h₁]⟩ }
    have hJ : J = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
      have hM0 : M ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)
      have hv := h ⟨M, hM.isPrime, hM0⟩
      unfold GlobalTheory.CompanionTheory.Equi.LocMem at hv
      obtain ⟨s, hs, y, hy, hsy⟩ := hv
      exact hs (hJM ⟨y, hy, hsy⟩)
    have h1 : (1 : 𝓞 F) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨y, hy, hy1⟩ := h1
    exact ⟨y, hy, by simpa using hy1.symm⟩
  · rintro ⟨y, hy, rfl⟩ v
    unfold GlobalTheory.CompanionTheory.Equi.LocMem
    exact ⟨1, fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), y, hy, by simp⟩

theorem cosetOff_empty_eq_latCoset (F : Type) [Field F] [NumberField F] (ι : Type)
    (I : Ideal (𝓞 F)) (x0 : ι → F) :
    cosetOff (∅ : Finset (HeightOneSpectrum (𝓞 F))) I x0 = latCoset I x0 := by
  ext x
  simp only [GlobalTheory.CompanionTheory.Equi.cosetOff, GlobalTheory.CompanionTheory.Equi.latCoset, Set.mem_setOf_eq]
  constructor
  · intro h i
    exact (forall_locMem_iff_exists_mem_ideal I (x i - x0 i)).mp fun v => h v (by simp) i
  · intro h v _ i
    exact (forall_locMem_iff_exists_mem_ideal I (x i - x0 i)).mpr (h i) v

end GlobalTheory.CompanionTheory.Equi
