module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TameSum

theorem isTameWD_of_lpSum {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {x y : WD h}
    (hxy : IsTameWD (x.lpSum y)) : IsTameWD x ∧ IsTameWD y := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  obtain ⟨m, b, rfl⟩ := WD.exists_rep y
  obtain ⟨k, c, hc, hw⟩ := hxy
  rw [WD.lpSum_mk, WD.mk_eq_mk] at hc
  have H : ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → (a.ρ σ).prodMap (b.ρ σ) = 1 :=
    fun σ hσ => hc.ρ_eq_one (hw σ hσ)
  refine ⟨⟨n, a, rfl, fun σ hσ => LinearMap.ext fun u => ?_⟩, ⟨m, b, rfl, fun σ hσ => LinearMap.ext fun u => ?_⟩⟩
  · simpa using congrArg Prod.fst (LinearMap.congr_fun (H σ hσ) (u, 0))
  · simpa using congrArg Prod.snd (LinearMap.congr_fun (H σ hσ) (0, u))

theorem isTameWD_of_mem_sumList : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (l : List (WD h)), IsTameWD (sumList l) → ∀ y ∈ l, IsTameWD y := by
  intro E Ω _ _ _ _ _ A w h l
  induction l with
  | nil => intro _ y hy; simp at hy
  | cons z l ih =>
    intro H y hy
    have H2 := isTameWD_of_lpSum (x := z) (y := sumList l) H
    rcases List.mem_cons.1 hy with rfl | hy
    · exact H2.1
    · exact ih H2.2 y hy

end GlobalTheory.TameSum
