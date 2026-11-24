module

public import Formalism.PeriodIntegrals.LocLatEq
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

@[expose] public section

noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq.W

def UnitP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p) (d : 𝓞 F),
    d ∉ p.asIdeal → ∃ u ∈ A.O, u * A.ιE ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) = 1

def AvoidP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 E)),
    (∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal →
      ¬ I ≤ P.asIdeal) →
    ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) d ∈ I

def CoreP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p)
    (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Λ.FG → ∀ y : Fin n → E, bc A y ∈ latL A Λ →
    ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) d • y ∈ Λ

theorem bc_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ}
    (s : 𝓞 E) (x : Fin n → E) : bc A (s • x) = A.ιE (s : E) • bc A x := by
  funext i
  simp [bc, Algebra.smul_def]

theorem latL_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ} (hU : UnitP)
    (Λ Λ' : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ x ∈ Λ, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) d • x ∈ Λ') :
    latL A Λ ≤ latL A Λ' := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨d, hd, hdx⟩ := h x hx
  obtain ⟨u, hu, hu1⟩ := hU F E sig p A d hd
  have hmem : ((⟨u, hu⟩ : A.O) • bc A (algebraMap (𝓞 F) (𝓞 E) d • x)) ∈ latL A Λ' :=
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hdx, rfl⟩)
  have heq : (⟨u, hu⟩ : A.O) • bc A (algebraMap (𝓞 F) (𝓞 E) d • x) = bc A x := by
    rw [Subring.smul_def, bc_smul, smul_smul]
    simp only [hu1, one_smul]
  rw [SetLike.mem_coe, ← heq]
  exact hmem

theorem locLatEq_of (hU : UnitP) (hA : AvoidP) (hC : CoreP) : PI.LocLatEq.Stmt := by
  intro F E _ _ _ _ _ h2 sig p A n Λ₁ Λ₂ hf1 hf2
  constructor
  · intro heq P hP x
    have key : ∀ (Λ Λ' : Submodule (𝓞 E) (Fin n → E)), Λ'.FG → latL A Λ = latL A Λ' →
        (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ) → (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ') := by
      rintro Λ Λ' hf' he ⟨s, hs, hsx⟩
      have hy : bc A (s • x) ∈ latL A Λ' := he ▸ Submodule.subset_span ⟨_, hsx, rfl⟩
      obtain ⟨d, hd, hdy⟩ := hC F E h2 sig p A n Λ' hf' (s • x) hy
      refine ⟨algebraMap (𝓞 F) (𝓞 E) d * s, ?_, by rwa [mul_smul]⟩
      intro hm
      rcases P.isPrime.mem_or_mem hm with h | h
      · apply hd
        rw [← hP]
        exact h
      · exact hs h
    exact ⟨key Λ₁ Λ₂ hf2 heq, key Λ₂ Λ₁ hf1 heq.symm⟩
  · intro h
    have side : ∀ (Λ Λ' : Submodule (𝓞 E) (Fin n → E)),
        (∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal →
          ∀ x : Fin n → E, (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ) →
            (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ')) → latL A Λ ≤ latL A Λ' := by
      intro Λ Λ' hh
      apply latL_le A hU
      intro x hx
      apply hA F E p (Λ'.comap (LinearMap.toSpanSingleton (𝓞 E) _ x))
      intro P hP hle
      have h1 : (1 : 𝓞 E) ∉ P.asIdeal := fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
      obtain ⟨s, hs, hsx⟩ := hh P hP x ⟨1, h1, by simpa using hx⟩
      exact hs (hle (by simpa [LinearMap.toSpanSingleton_apply] using hsx))
    exact le_antisymm (side Λ₁ Λ₂ (fun P hP x => (h P hP x).1))
      (side Λ₂ Λ₁ (fun P hP x => (h P hP x).2))

end PI.LocLatEq.W
