module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory

theorem selfDual_exists_snd_of_orth : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))),
    (∀ z, z ∈ Λ ↔ ∀ l ∈ Λ, ψ₀ (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1) →
    (∀ a ∈ v.adicCompletionIntegers F, ∀ l ∈ Λ, a • l ∈ Λ) →
    (∃ c : Fv F v, c ≠ 0 ∧ ∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F) →
    ∀ u : κ → Fv F v, (∀ y, ((0 : κ → Fv F v), y) ∈ Λ → ψ₀ (u ⬝ᵥ y) = 1) → ∃ y', (u, y') ∈ Λ := by
  intro F _ _ v κ _ ψ₀ Λ hdual hsmul hbd u hu
  classical
  obtain ⟨c, hc0, hc⟩ := hbd
  let O := v.adicCompletionIntegers F
  let Λ' : Submodule O ((κ → Fv F v) × (κ → Fv F v)) :=
    { carrier := Λ
      add_mem' := fun ha hb => Λ.add_mem ha hb
      zero_mem' := Λ.zero_mem
      smul_mem' := fun a l hl => hsmul (a : Fv F v) a.2 l hl }
  let Λ₁ : Submodule O (κ → Fv F v) := Λ'.map (LinearMap.fst O _ _)
  let φ : (κ → O) →ₗ[O] (κ → Fv F v) :=
    { toFun := fun x i => c⁻¹ * (x i : Fv F v)
      map_add' := by intro x y; funext i; simp [mul_add]
      map_smul' := by intro a x; funext i; simp [Algebra.smul_def]; ring }
  have hle : Λ₁ ≤ LinearMap.range φ := by
    rintro x ⟨l, hl, rfl⟩
    refine ⟨fun i => ⟨c * l.1 i, hc l hl i⟩, ?_⟩
    funext i
    simp [φ, hc0]
  haveI : IsNoetherian O (LinearMap.range φ) := isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : IsNoetherian O Λ₁ := isNoetherian_of_le hle
  haveI : Module.Finite O Λ₁ := Module.IsNoetherian.finite O Λ₁
  haveI : Module.IsTorsionFree O Λ₁ := inferInstance
  haveI : Module.Free O Λ₁ := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis O Λ₁
  have hlift : ∀ i, ∃ l ∈ Λ, l.1 = (b i : κ → Fv F v) := fun i => by
    obtain ⟨l, hl, he⟩ := Submodule.mem_map.1 (b i).2
    exact ⟨l, hl, he⟩
  choose L hL hL1 using hlift
  have hliO : LinearIndependent O (fun i => (b i : κ → Fv F v)) :=
    b.linearIndependent.map' Λ₁.subtype (Submodule.ker_subtype _)
  have hliK : LinearIndependent (Fv F v) (fun i => (b i : κ → Fv F v)) :=
    (LinearIndependent.iff_fractionRing O (Fv F v)).1 hliO
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.linearCombination (Fv F v) (fun i => u ⬝ᵥ (L i).2)) ∘ₗ (Module.Basis.span hliK).repr.toLinearMap)
  have hgb : ∀ i, g (b i) = u ⬝ᵥ (L i).2 := by
    intro i
    have h1 := LinearMap.congr_fun hg (Module.Basis.span hliK i)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
      Finsupp.linearCombination_single, one_smul, Submodule.subtype_apply] at h1
    rw [Module.Basis.span_apply] at h1
    exact h1
  let y' : κ → Fv F v := fun j => g (fun k => if j = k then 1 else 0)
  have hy : ∀ x, x ⬝ᵥ y' = g x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ g x]
    simp [dotProduct, smul_eq_mul, y']
  refine ⟨y', (hdual _).2 ?_⟩
  intro l hl
  have hl1 : l.1 ∈ Λ₁ := Submodule.mem_map.2 ⟨l, hl, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = b.repr ⟨l.1, hl1⟩ := ⟨_, rfl⟩
  have hsum : l.1 = ∑ i, (a i : Fv F v) • (b i : κ → Fv F v) := by
    have h := congrArg Subtype.val (b.sum_repr ⟨l.1, hl1⟩)
    rw [← ha] at h
    refine h.symm.trans ?_
    rw [Submodule.coe_sum]
    rfl
  let m := l - ∑ i, (a i : Fv F v) • L i
  have hm : m ∈ Λ := Λ.sub_mem hl (Λ.sum_mem fun i _ => hsmul _ (a i).2 _ (hL i))
  have hm1 : m.1 = 0 := by
    simp [m, Prod.fst_sum, hL1, ← hsum]
  have hm2 : m.2 = l.2 - ∑ i, (a i : Fv F v) • (L i).2 := by simp [m, Prod.snd_sum]
  have key : u ⬝ᵥ l.2 - l.1 ⬝ᵥ y' = u ⬝ᵥ m.2 := by
    rw [hy, hm2, dotProduct_sub, dotProduct_sum]
    congr 1

    rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul, hgb, dotProduct_smul]
  rw [key]
  apply hu
  have : ((0 : κ → Fv F v), m.2) = m := Prod.ext hm1.symm rfl
  rw [this]; exact hm

end GlobalTheory
