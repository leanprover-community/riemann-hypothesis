module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRingHomPowPrimePow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfFacts
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

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem wp_pf : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    (K : Type) [CommRing K] [Algebra A K] (n : ℕ) (ι : Fin n → (B →ₐ[A] K)),
    IsWP ι → Pf p A → Pf p B → Pf p K := by
  intro p _ A _ B _ _ K _ _ n ι hW hA hB
  obtain ⟨⟨FA, hFA⟩, -⟩ := pf_facts p A hA
  obtain ⟨⟨FB, hFB⟩, -⟩ := pf_facts p B hB
  have hchar : (p : K) = 0 := by
    have := congrArg (algebraMap A K) hA.char
    simpa using this
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p K hchar 1
  have hF' : ∀ x, F x = x ^ p := fun x => by rw [hF, pow_one]
  have hcompat : ∀ i, (((ι i : B →+* K)).comp (FB.symm : B →+* B)).comp (algebraMap A B) =
      (algebraMap A K).comp (FA.symm : A →+* A) := by
    intro i
    ext a
    obtain ⟨b, rfl⟩ := FA.surjective a
    have h1 : algebraMap A B (FA b) = FB (algebraMap A B b) := by
      rw [hFA, hFB, map_pow]
    simp [h1]
  obtain ⟨z, hz1, hz2⟩ := hW.ex K ((algebraMap A K).comp (FA.symm : A →+* A))
    (fun i => ((ι i : B →+* K)).comp (FB.symm : B →+* B)) hcompat
  have hz1' : ∀ a, z (algebraMap A K a) = algebraMap A K (FA.symm a) := fun a => by
    simpa using congrArg (fun f : A →+* K => f a) hz1
  have hz2' : ∀ i b, z (ι i b) = ι i (FB.symm b) := fun i b => by
    simpa using congrArg (fun f : B →+* K => f b) (hz2 i)
  have hFa : ∀ a, F (algebraMap A K a) = algebraMap A K (FA a) := fun a => by
    rw [hF', hFA, map_pow]
  have hFb : ∀ i b, F (ι i b) = ι i (FB b) := fun i b => by
    rw [hF', hFB, map_pow]
  have hFz : F.comp z = RingHom.id K := by
    apply hW.uniq K
    · ext a
      simp [hz1', hFa]
    · intro i
      ext b
      simp [hz2', hFb]
  have hzF : z.comp F = RingHom.id K := by
    apply hW.uniq K
    · ext a
      simp [hz1', hFa]
    · intro i
      ext b
      simp [hz2', hFb]
  refine ⟨hchar, ?_, ?_⟩
  · intro x y hxy
    have h : F x = F y := by rw [hF', hF']; exact hxy
    have := congrArg z h
    have hx : ∀ w, z (F w) = w := fun w => by
      simpa using congrArg (fun f : K →+* K => f w) hzF
    rwa [hx, hx] at this
  · intro y
    refine ⟨z y, ?_⟩
    have : F (z y) = y := by simpa using congrArg (fun f : K →+* K => f y) hFz
    simpa [hF'] using this

end GlobalTheory.CompanionTheory.PerfectRing
