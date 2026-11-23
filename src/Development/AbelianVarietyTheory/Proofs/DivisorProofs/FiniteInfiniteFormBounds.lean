module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FormVal

theorem bigC_and {Q Q' : ChQ} (h : BigC Q) (h' : BigC Q') : BigC fun F ch C b => Q F ch C b ∧ Q' F ch C b := by
  obtain ⟨A0, hA⟩ := h
  obtain ⟨B0, hB⟩ := h'
  refine ⟨max A0 B0, fun CF hCF => ?_⟩
  obtain ⟨C1, hC1⟩ := hA CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, hC2⟩ := hB CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, fun ε C hC => ?_⟩
  obtain ⟨x1, hx1⟩ := hC1 ε C (le_trans (le_max_left _ _) hC)
  obtain ⟨x2, hx2⟩ := hC2 ε C (le_trans (le_max_right _ _) hC)
  refine ⟨max x1 x2, ?_⟩
  intro D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hOK
  exact ⟨hx1 D large₂ hε (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hOK,
    hx2 D large₂ hε (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hOK⟩

theorem bigC_mono {Q Q' : ChQ} (h : BigC Q) (hQ : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (F : Face D A) (ch : Choice R) (C b : ℝ), Q F ch C b → Q' F ch C b) : BigC Q' := by
  obtain ⟨a, h⟩ := h
  refine ⟨a, fun CF hCF => ?_⟩
  obtain ⟨c, h⟩ := h CF hCF
  refine ⟨c, fun ε C hC => ?_⟩
  obtain ⟨x, h⟩ := h ε C hC
  exact ⟨x, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j k => hQ F ch C large₂.sc.b (h D large₂ e hx Γ Pl0 T A Ks R F s ch i j k)⟩


theorem form_fin_inf_of (h1 : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch _ _ => ∀ (t : _) (w : PlL D), ∀ x ∈ (A.fam.R t).Mt (A.fam.lvl F.P0 F.ψ0), ∀ y,
  InLat _ w 0 (latAt ch.S.toGridChoice (.grid 0 D.R.m) y) (rowVal ch.S.toGridChoice (ch.S.formC t (R.jX t (formOf F t x)) y))) (h2 : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch _ _ => ∀ (σ : D.what₂.LL →+* ℂ) (x : Fin ((A.fam.R A.μ0).nV (A.fam.lvl F.P0 F.ψ0)) → D.what₂.LL),
  0 ≤ (star (fun i => σ (x i)) ⬝ᵥ (((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)).map σ).mulVec fun i => σ (x i)).re ∧ ∀ y,
  NrmLe _ σ (rowVal ch.S.toGridChoice (ch.S.formC A.μ0 (R.jX A.μ0 (formOf F A.μ0 x)) y))
    ((Nat.card (A.fam.lvl F.P0 F.ψ0).P : ℝ) * ((A.fam.R A.μ0).S.DGam : ℝ) *
      (star (fun i => σ (x i)) ⬝ᵥ (((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)).map σ).mulVec fun i => σ (x i)).re)) (h3 : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch C b => 0 ≤ bOne ch.G C b ∧
  (Nat.card (A.fam.lvl F.P0 F.ψ0).P : ℝ) * ((A.fam.R A.μ0).S.DGam : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)) : FinFormK ∧ InfFormK := by
  refine ⟨bigC_mono (bigC_and h1 h3) ?_, bigC_mono (bigC_and h2 h3) ?_⟩
  · rintro D Γ _ _ Pl0 T A Ks _ _ _ R F ch C b ⟨hv, hb, -⟩
    refine ⟨fun _ => 0, ⟨fun _ => le_rfl, by simp, fun s => by simpa using hb⟩, fun t w x hx y => ?_⟩
    exact hv t w x hx y
  · rintro D Γ _ _ Pl0 T A Ks _ _ _ R F ch C b ⟨hv, -, hK⟩ σ x y
    obtain ⟨hq, hy⟩ := hv σ x
    obtain ⟨u, e, hu⟩ := hy y
    exact ⟨u, e, hu.trans (mul_le_mul_of_nonneg_right hK hq)⟩

end GlobalTheory.FormVal

end
