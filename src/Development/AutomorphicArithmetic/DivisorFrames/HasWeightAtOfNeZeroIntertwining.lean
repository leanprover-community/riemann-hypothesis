module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

private theorem cEmb_of_mem_embU {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {τ σ : E →+* ℂ}
    (h : InfinitePlace.mk σ ≠ InfinitePlace.mk τ) {x : UA E n} (hx : x ∈ embU n τ) : cEmb σ x = 1 := by
  have h1 := (Subgroup.mem_inf.1 hx).2
  rw [Subgroup.mem_iInf] at h1
  have h2 := h1 σ
  rw [Subgroup.mem_iInf] at h2
  exact h2 h

theorem UpperTheory.hasWeightAt_of_ne_zero_intertwining :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι] (emb : ι → (E →+* ℂ)), Function.Injective (fun τ => InfinitePlace.mk (emb τ)) →
        ∀ (lam : ι → DomWeight n) (π : Submodule ℂ (UA E n → ℂ)) (f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] (UA E n → ℂ)), f ≠ 0 → (∀ v, f v ∈ π) →
        (∀ x ∈ infU E n, ∀ v, f (Formalism.L2.DIV.rhoK lam (fun τ => cEmb (emb τ) x) v) = RU E n x (f v)) →
        ∀ τ, HasWeightAt π (emb τ) (lam τ) := by
  intro E _ _ _ n ι _ emb hinj lam π f hf0 hf heq τ
  classical
  obtain ⟨e, he⟩ : ∃ e, f (GlobalTheory.CoefIrred.tenMul lam e) ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hf0
    apply (Formalism.L2.DIV.bVV ℂ lam).ext
    intro i
    have hB : Formalism.L2.DIV.bVV ℂ lam i = GlobalTheory.CoefIrred.tenMul lam
        (fun τ => GlobalTheory.CoefIrred.ssBasis ℂ (lam τ) (i τ)) := by
      apply Subtype.ext
      rw [Formalism.L2.DIV.bVV_coe, GlobalTheory.CoefIrred.tenMul_coe, Formalism.L2.DIV.bVVfun]
      simp only [GlobalTheory.CoefIrred.ssBasis_coe]
    rw [hB]
    exact hc _
  refine ⟨isIrreducible_sqRep n (lam τ), f ∘ₗ (GlobalTheory.CoefIrred.tenMul lam).toLinearMap e τ, fun h0 => he ?_,
    fun a => hf _, fun x a => ?_⟩
  · have := LinearMap.congr_fun h0 (e τ)
    simpa [MultilinearMap.toLinearMap] using this
  · have hx : x.1 ∈ infU E n := embU_le_infU _ x.2
    have h2 := heq x.1 hx (GlobalTheory.CoefIrred.tenMul lam (Function.update e τ a))
    have h3 : Formalism.L2.DIV.rhoK lam (fun σ => cEmb (emb σ) x.1) (GlobalTheory.CoefIrred.tenMul lam (Function.update e τ a)) =
        GlobalTheory.CoefIrred.tenMul lam
          (Function.update e τ (GlobalTheory.Branching.sqRep ℂ n (lam τ) (cEmb (emb τ) x.1) a)) := by
      rw [rhoK_tenMul]
      congr 1
      funext σ
      by_cases h : σ = τ
      · subst h
        simp only [Function.update_self]
      · have h4 : cEmb (emb σ) x.1 = 1 := cEmb_of_mem_embU (fun h5 => h (hinj h5)) x.2
        simp only [Function.update_of_ne h, h4, map_one, Module.End.one_apply]
    rw [h3] at h2
    exact h2
