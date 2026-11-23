module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLocalGenerator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

private lemma exists_local_generator {B : Type} [CommRing B] [IsDedekindDomain B]
    (I : Ideal B) (p : Ideal B) [hp : p.IsPrime] :
    ∃ π ∈ I, ∃ s, s ∉ p ∧ ∀ x ∈ I, s * x ∈ Ideal.span {π} :=
  _root_.UpperTheory.Reformulated.B.ExistsLocalGenerator.exists_local_generator I p

theorem UpperTheory.dedekind_spec_open_isAffine :
    ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (W : (Spec (CommRingCat.of B)).Opens), IsAffineOpen W := by
  intro B _ _ W
  let S : Set (PrimeSpectrum B) := ((W : Set (Spec (CommRingCat.of B)))ᶜ : Set (Spec (CommRingCat.of B)))
  have hS : IsClosed S := W.isOpen.isClosed_compl
  let I : Ideal B := PrimeSpectrum.vanishingIdeal S
  have hWc : PrimeSpectrum.zeroLocus (I : Set B) = S := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hS.closure_eq
  let D : B → (Spec (CommRingCat.of B)).Opens := fun r =>
    PrimeSpectrum.basicOpen (R := CommRingCat.of B) r
  have hbasic : ∀ r : B, IsAffineOpen (D r) := by
    intro r
    have h := (isAffineOpen_top (Spec (CommRingCat.of B))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv r)
    rwa [basicOpen_eq_of_affine] at h
  have hmain : IsAffineHom W.ι := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
    obtain ⟨π, hπ, s, hs, hsI⟩ := @exists_local_generator B _ _ I x.asIdeal x.isPrime
    refine ⟨D s, hs, hbasic s, ?_⟩
    have hEq : W ⊓ D s = D (s * π) := by
      ext q
      have hq : q ∈ W ↔ ¬ (I : Set B) ⊆ q.asIdeal := by
        have h1 : (I : Set B) ⊆ q.asIdeal ↔ q ∉ W := Set.ext_iff.1 hWc q
        rw [h1, not_not]
      have hDm : ∀ r : B, q ∈ D r ↔ r ∉ q.asIdeal := fun r => Iff.rfl
      change q ∈ W ∧ q ∈ D s ↔ q ∈ D (s * π)
      rw [hDm, hDm, hq]
      have hqp : q.asIdeal.IsPrime := q.isPrime
      constructor
      · rintro ⟨hIq, hsq⟩ hm
        rcases hqp.mem_or_mem hm with h | h
        · exact hsq h
        · refine hIq fun y hy => ?_
          have h2 : s * y ∈ q.asIdeal :=
            (Ideal.span_singleton_le_iff_mem q.asIdeal).2 h (hsI y hy)
          exact (hqp.mem_or_mem h2).resolve_left hsq
      · intro hm
        refine ⟨fun hsub => hm (Ideal.mul_mem_left _ _ (hsub hπ)),
          fun h => hm (Ideal.mul_mem_right _ _ h)⟩
    have h := hbasic (s * π)
    rw [← hEq] at h
    have h2 := h.preimage_of_isOpenImmersion W.ι (by simp)
    have e : W.ι ⁻¹ᵁ (W ⊓ D s) = W.ι ⁻¹ᵁ D s := by
      ext y
      exact ⟨fun hy => hy.2, fun hy => ⟨y.2, hy⟩⟩
    rwa [e] at h2
  have : IsAffine W.toScheme := isAffine_of_isAffineHom W.ι
  exact this
