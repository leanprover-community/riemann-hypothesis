module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneParamDualListSumAbsTwistSpecial
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

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.weilDeligneParam_dual_listSum_absTwist_special : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ l : List (WD h), (sumList l).lpDual = sumList (l.map WD.lpDual)) ∧ (∀ (y : WD h) (s : ℝ), (y.lpTw s).lpDual = y.lpDual.lpTw (-s)) ∧ ∀ (y : WD h) (n : ℕ), (y.lpChar (WD.lpSp (h := h) n)).lpDual = y.lpDual.lpChar (WD.lpSp (h := h) n) := by
  intro E Ω _ _ _ _ _ A w h
  have dual_sp (y : WD h) (n : ℕ) :
      (y.lpChar (WD.lpSp (h := h) n)).lpDual = y.lpDual.lpChar (WD.lpSp (h := h) n) := by
    induction y using WD.ind with
    | hP m a =>
      rw [WD.lpSp, WD.lpChar_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpChar_mk]
      exact WD.sound ((GlobalTheory.WDDual.iso_tensor_dual a (WDRep.sp (h := h) n)).symm.trans
        ((WDRep.Iso.refl a.dual).tensor (GlobalTheory.WDDual.iso_sp_dual (h := h) n)))
  exact ⟨GlobalTheory.WDDual.WDClass.lpDual_sumList, GlobalTheory.WDDual.WDClass.lpDual_lpTw,
    dual_sp⟩
