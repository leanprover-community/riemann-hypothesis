module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIdealWeightSectionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp.Sandwich

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {TF : TorFlag Xo c} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {P : WtPar Dw} (R : Choice TF.X Z U P)

theorem restr_mulPole (j : ℕ) (f : H0 R.str (R.adj j) ⊤) :
    H0.restr le_top (R.mulPole j ⊤ f) = R.mulPole j R.off (H0.restr le_top f) :=
  (ProdChart.restr_mul _ _ _ _).trans (by rw [H0.restr_ofSec]; rfl)

theorem mulPole_injective (h₁ : FreeOnOpen TF.X Z U P.u₁) (j : ℕ) : Function.Injective (R.mulPole j R.off) :=
  ((R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).mulEquiv (R.Δ₁.nowhereZero_pow R.str (R.notMem_support h₁) j)).injective

theorem nowhereZero_pow_zero : NowhereZero (H0.ofSec R.str ⊤ (R.Δ₁.pow 0)) := nowhereZero_of_exists fun y hy => by
  obtain ⟨i, hi⟩ := exists_chart R.Δ₁.isLB y
  exact ⟨fun _ => i, mem_zpow_U.2 hi, by rw [R.Δ₁.germ_pow R.str 0 i y hy hi, pow_zero]; exact isUnit_one⟩

end GlobalTheory.HSApp.Sandwich


open GlobalTheory.HSApp.Sandwich in
theorem GlobalTheory.HSApp.sandwich : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice TF.X Z U P)
    (ω : CanId R.toModif), FnAlgClosed (Xo := Xo) (c := c) → ∀ h₁ : FreeOnOpen TF.X Z U P.u₁,
    (∀ j, CuspIso TF.X Z U (P.wt j) → adjGlobal R j ≤ LinearMap.range (adjSec R ω h₁ j)) ∧
    (CuspIso TF.X Z U (P.wt 0) → LinearMap.range (adjSec R ω h₁ 0) ≤ adjGlobal R 0) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z r U P R ω hF h₁
  have key := fun (j : ℕ) m => GlobalTheory.T.canonical_ideal_weight_section hP hG E H Dw l Xo c TF Z hF R.toModif ω _ _ (P.kap_add j) m
  refine ⟨fun j hj => ?_, fun hj => ?_⟩
  · rintro _ ⟨f, rfl⟩
    let e := R.adjEquiv ω.ω ω.unit h₁ j (P.kap_add j)
    obtain ⟨m, hm⟩ := (R.bijective_pullOff (isLB_L₀ TF.X Z (P.wt j))).2 (e.symm (H0.restr le_top f))
    have hmul : H0.restr le_top (R.mulPole j ⊤ f) =
        (((common₀ TF.X Z).pull R.σ).canChart R.K.isLB (P.kap_add j)).mul ω.ω (R.pullOff m) := by
      rw [restr_mulPole, hm]
      have := R.mulPole_adjEquiv ω.ω ω.unit h₁ j (P.kap_add j) (e.symm (H0.restr le_top f))
      rw [LinearEquiv.apply_symm_apply] at this
      exact this
    obtain ⟨g, hg, hgm⟩ := (key j m).2 ⟨R.mulPole j ⊤ f, hmul⟩
    obtain ⟨c', hc'⟩ := hj.2 hg
    refine ⟨c', ?_⟩
    show e (R.pullOff (cuspSec TF.X Z U _ c')) = _
    rw [hc', hgm, hm, LinearEquiv.apply_symm_apply]
  · rintro _ ⟨c', rfl⟩
    obtain ⟨s, hs, hsr⟩ := hj.1 c'
    obtain ⟨g, hg⟩ := (key 0 _).1 ⟨s, hs, hsr⟩
    obtain ⟨f, hf⟩ := ((R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).mulEquiv (nowhereZero_pow_zero R)).surjective g
    refine ⟨f, mulPole_injective R h₁ 0 ?_⟩
    rw [← restr_mulPole, mulPole_adjSec]
    exact (congrArg (H0.restr le_top) hf).trans hg
