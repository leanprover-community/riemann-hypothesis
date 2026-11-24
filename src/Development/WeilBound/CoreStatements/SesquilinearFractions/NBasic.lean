module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

theorem isScalarTower_rat_of_ringHom {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] (f : k →+* k') :
    letI : Algebra k k' := f.toAlgebra;
    IsScalarTower ℚ k k' := by
  letI : Algebra k k' := f.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

theorem exists_extension_embedding_alg_closed : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (j : k →+* A), ∃ j' : k' →+* A, j'.comp f = j := by
  intro k k' A _ _ _ _ _ _ _ f j
  letI : Algebra k k' := f.toAlgebra
  letI : Algebra k A := j.toAlgebra
  haveI : IsScalarTower ℚ k k' := isScalarTower_rat_of_ringHom f
  haveI : Module.Finite k k' := Module.Finite.of_restrictScalars_finite ℚ k k'
  haveI : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
  refine ⟨(IsAlgClosed.lift : k' →ₐ[k] A).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : k' →ₐ[k] A).commutes x

open Classical in
theorem card_embeddings_extending {k k' A : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A]
    [IsAlgClosed A] (f : k →+* k') (j : k →+* A) :
    letI : Algebra k k' := f.toAlgebra;
    (Finset.univ.filter fun j' : k' →+* A => j'.comp f = j).card = Module.finrank k k' := by
  letI : Algebra k k' := f.toAlgebra
  letI : Algebra k A := j.toAlgebra
  haveI : IsScalarTower ℚ k k' := isScalarTower_rat_of_ringHom f
  haveI : Module.Finite k k' := Module.Finite.of_restrictScalars_finite ℚ k k'
  rw [← Fintype.card_subtype, Fintype.card_eq_nat_card,
    ← AlgHom.natCard_of_splits k k' A (fun _ => IsAlgClosed.splits _)]
  refine Nat.card_congr
    { toFun := fun ψ => { ψ.1 with commutes' := fun r => RingHom.congr_fun ψ.2 r }
      invFun := fun φ => ⟨φ.toRingHom, RingHom.ext φ.commutes⟩
      left_inv := fun ψ => rfl
      right_inv := fun φ => rfl }

theorem sum_embeddings_base_change : ∀ (k k' A : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (F : (k →+* A) → ℝ), (Module.finrank ℚ k : ℝ) * ∑ j : k' →+* A, F (j.comp f) = (Module.finrank ℚ k' : ℝ) * ∑ j : k →+* A, F j := by
  intro k k' A _ _ _ _ _ _ _ f F
  classical
  letI : Algebra k k' := f.toAlgebra
  haveI : IsScalarTower ℚ k k' := isScalarTower_rat_of_ringHom f
  have hsum : ∑ j' : k' →+* A, F (j'.comp f) = (Module.finrank k k' : ℝ) * ∑ j : k →+* A, F j := by
    rw [← Finset.sum_fiberwise Finset.univ (fun j' : k' →+* A => j'.comp f), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => F j) (fun j' hj' => by rw [(Finset.mem_filter.1 hj').2]),
      Finset.sum_const, nsmul_eq_mul]
    congr 2
    convert card_embeddings_extending f j
  rw [hsum, ← Module.finrank_mul_finrank ℚ k k']
  push_cast
  ring

theorem finsum_const_mul {α : Type} (c : ℝ) (_hc : c ≠ 0) (g : α → ℝ) : ∑ᶠ p, c * g p = c * ∑ᶠ p, g p :=
  (mul_finsum g c).symm

theorem logNorms_ext_degree_adelic : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (f : k →+* k') (N : LogNorms k), (N.ext f).deg = N.deg ∧ ((N.ext f).IsAdelic ↔ N.IsAdelic) := by
  intro k k' _ _ _ _ f N
  have hd : (0:ℝ) < Module.finrank ℚ k := by exact_mod_cast Module.finrank_pos
  have hd' : (0:ℝ) < Module.finrank ℚ k' := by exact_mod_cast Module.finrank_pos
  set c : ℝ := (Module.finrank ℚ k' : ℝ) / Module.finrank ℚ k with hc_def
  have hc : c ≠ 0 := (div_pos hd' hd).ne'
  have hinf : ∑ s : k' →+* ℂ, N.inf (s.comp f) = c * ∑ s : k →+* ℂ, N.inf s := by
    rw [hc_def, div_mul_eq_mul_div, eq_div_iff hd.ne', ← sum_embeddings_base_change k k' ℂ f N.inf]
    ring
  have hfin : ∀ p : Nat.Primes, (N.ext f).finSum p = c * N.finSum p := by
    intro p
    show ∑ ι : k' →+* ℂ_[(p:ℕ)], N.fin p (ι.comp f) = c * ∑ ι : k →+* ℂ_[(p:ℕ)], N.fin p ι
    rw [hc_def, div_mul_eq_mul_div, eq_div_iff hd.ne', ← sum_embeddings_base_change k k' ℂ_[(p:ℕ)] f (N.fin p)]
    ring
  refine ⟨?_, ?_⟩
  · show -(∑ s : k' →+* ℂ, N.inf (s.comp f) + ∑ᶠ p, (N.ext f).finSum p) / (Module.finrank ℚ k' : ℝ) = N.deg
    rw [hinf, finsum_congr hfin, finsum_const_mul c hc, ← mul_add, LogNorms.deg, hc_def]
    field_simp
  · have hset : {p : Nat.Primes | ∃ ι : k' →+* ℂ_[(p:ℕ)], (N.ext f).fin p ι ≠ 0} =
        {p : Nat.Primes | ∃ ι : k →+* ℂ_[(p:ℕ)], N.fin p ι ≠ 0} := by
      ext p
      constructor
      · rintro ⟨ι, h⟩
        exact ⟨ι.comp f, h⟩
      · rintro ⟨ι, h⟩
        obtain ⟨ι', hι'⟩ := exists_extension_embedding_alg_closed k k' ℂ_[(p:ℕ)] f ι
        refine ⟨ι', ?_⟩
        show N.fin p (ι'.comp f) ≠ 0
        rw [hι']
        exact h
    unfold LogNorms.IsAdelic
    rw [hset]

end PositivityTheory.Xgf
