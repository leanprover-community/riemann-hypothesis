module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.WittVector.Basic
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
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
public import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.ColengthLemmas

variable {R : Type} [CommRing R]

theorem length_comp_range {A B C : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (u : B →ₗ[R] A) (v : C →ₗ[R] B) (hu : Function.Injective u) :
    Module.length R (A ⧸ LinearMap.range (u ∘ₗ v)) =
      Module.length R (A ⧸ LinearMap.range u) + Module.length R (B ⧸ LinearMap.range v) := by
  have hle : LinearMap.range v ≤ (LinearMap.range (u ∘ₗ v)).comap u := by
    rintro _ ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  have hle2 : LinearMap.range (u ∘ₗ v) ≤ LinearMap.range u := LinearMap.range_comp_le_range v u
  let f := (LinearMap.range v).mapQ (LinearMap.range (u ∘ₗ v)) u hle
  let g := Submodule.factor hle2
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [LinearMap.mem_ker] at hx
    simp only [f, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨c, hc⟩ := hx
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨c, hu hc⟩
  have hg : Function.Surjective g := Submodule.factor_surjective hle2
  have hex : Function.Exact f g := by
    intro x
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ x
    constructor
    · intro h
      have h' : a ∈ LinearMap.range u := by
        simpa [g, Submodule.factor_mk, Submodule.Quotient.mk_eq_zero] using h
      obtain ⟨b, rfl⟩ := h'
      exact ⟨Submodule.Quotient.mk b, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [← hy]
      show g (Submodule.Quotient.mk (u b)) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨b, rfl⟩
  rw [Module.length_eq_add_of_exact f g hf hg hex, add_comm]

theorem eq_of_le_of_length_eq {A : Type} [AddCommGroup A] [Module R A] (L L' : Submodule R A)
    (h : L ≤ L') (hl : Module.length R (A ⧸ L) = Module.length R (A ⧸ L'))
    (ht : Module.length R (A ⧸ L) ≠ ⊤) : L = L' := by
  let g := Submodule.factor h
  have e := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
    (LinearMap.ker g).injective_subtype (Submodule.factor_surjective h)
    (LinearMap.exact_subtype_ker_map g)
  have h0 : Module.length R (LinearMap.ker g) = 0 := by
    rw [← hl] at e
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 ht
    rw [← hn] at e
    generalize Module.length R (LinearMap.ker g) = b at e ⊢
    induction b using ENat.recTopCoe with
    | top => simp at e
    | coe b =>
      norm_cast at e ⊢
      omega
  rw [Module.length_eq_zero_iff] at h0
  refine le_antisymm h fun x hx => ?_
  have hmem : (Submodule.Quotient.mk x : A ⧸ L) ∈ LinearMap.ker g := by
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero _).2 hx
  have h1 : (⟨Submodule.Quotient.mk x, hmem⟩ : LinearMap.ker g) = 0 := Subsingleton.elim _ _
  have h2 : (Submodule.Quotient.mk x : A ⧸ L) = 0 := congrArg Subtype.val h1
  exact (Submodule.Quotient.mk_eq_zero _).1 h2

theorem length_quot_smul_range_free (O M : Type) [CommRing O] [Nontrivial O] [AddCommGroup M]
    [Module O M] [Module.Free O M] [Module.Finite O M] (a : O) :
    Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) =
      (Module.finrank O M : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical
  set d := Module.finrank O M
  let e : M ≃ₗ[O] (Fin d → O) := (Module.finBasis O M).equivFun
  have hmap : (LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))).map (e : M →ₗ[O] (Fin d → O))
      = Submodule.pi Set.univ (fun _ : Fin d => (Ideal.span {a} : Submodule O O)) := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, true_implies,
      LinearMap.smul_apply, LinearMap.id_apply]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩ i
      rw [LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
    · intro h
      choose c hc using fun i => Ideal.mem_span_singleton'.1 (h i)
      refine ⟨a • e.symm c, ⟨e.symm c, rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, map_smul, LinearEquiv.apply_symm_apply]
      funext i
      simp [← hc i, mul_comm]
  let f := (Submodule.Quotient.equiv _ _ e hmap).trans
    (Submodule.quotientPi (fun _ : Fin d => (Ideal.span {a} : Submodule O O)))
  rw [f.length_eq, Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

theorem length_quot_p_pow (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (n : ℕ) : Module.length (WittVector p k) (WittVector p k ⧸ Ideal.span {(p : WittVector p k) ^ n}) = n := by
  rw [← Ideal.span_singleton_pow, ← (WittVector.irreducible p).maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal _ n

end GlobalTheory.Dieu.ColengthLemmas

namespace GlobalTheory.Dieu

open GlobalTheory.Dieu.ColengthLemmas in
theorem colength_add_and_pow_and_eq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B C : Type) [AddCommGroup A] [Module (WittVector p k) A] [AddCommGroup B] [Module (WittVector p k) B] [AddCommGroup C] [Module (WittVector p k) C], (∀ (u : B →ₗ[(WittVector p k)] A) (v : C →ₗ[(WittVector p k)] B), Function.Injective u → Module.length (WittVector p k) (A ⧸ LinearMap.range (u ∘ₗ v)) = Module.length (WittVector p k) (A ⧸ LinearMap.range u) + Module.length (WittVector p k) (B ⧸ LinearMap.range v)) ∧ (Module.Free (WittVector p k) A → Module.Finite (WittVector p k) A → ∀ (n : ℕ) (u : A →ₗ[(WittVector p k)] A), (∀ a, u a = p ^ n • a) → Module.length (WittVector p k) (A ⧸ LinearMap.range u) = (n * Module.finrank (WittVector p k) A : ℕ)) ∧ ∀ L L' : Submodule (WittVector p k) A, L ≤ L' → Module.length (WittVector p k) (A ⧸ L) = Module.length (WittVector p k) (A ⧸ L') → Module.length (WittVector p k) (A ⧸ L) ≠ ⊤ → L = L' := by
  intro p _ k _ _ _ A B C _ _ _ _ _ _
  refine ⟨fun u v hu => length_comp_range u v hu, fun _ _ n u hu => ?_,
    fun L L' h hl ht => eq_of_le_of_length_eq L L' h hl ht⟩
  have hu' : u = ((p : WittVector p k) ^ n) • (LinearMap.id : A →ₗ[WittVector p k] A) := by
    ext a
    rw [hu a, LinearMap.smul_apply, LinearMap.id_apply, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [hu', length_quot_smul_range_free, length_quot_p_pow]
  push_cast
  ring

end GlobalTheory.Dieu
