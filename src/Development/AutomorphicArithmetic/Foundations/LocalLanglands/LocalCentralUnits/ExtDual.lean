module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneParamDualListSumAbsTwistSpecialStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodSeg
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {r : IrrGL (k := w.adicCompletion E) → WD h}

private theorem summand_dual (H : CuspT a ha r) {Δ Δ' : Segment (w.adicCompletion E)}
    (hg : GoodCusp Δ.first) (hd : SegDual Δ Δ') :
    ((r Δ'.first).lpTw (((Δ'.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ'.len) =
      (((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).lpDual := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨hl, hD⟩ := hd
  have hc : (Δ.first.nu ((Δ.len : ℂ) - 1)).IsCusp := Δ.isCusp_first.nu _
  have hgn : GoodCusp (Δ.first.nu ((Δ.len : ℂ) - 1)) := by
    rw [IrrGL.nu]
    exact ((clBasic _ Δ.first).2.1 _ _).2.2.1.2 hg
  have e1 := H.dual _ _ hc Δ'.isCusp_first hgn hD
  have e2 : Δ.first.nu ((Δ.len : ℂ) - 1) = Δ.first.nu (((Δ.len : ℝ) - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [e2, H.nu _ Δ.isCusp_first] at e1
  obtain ⟨hS, hT, hP⟩ := GlobalTheory.T.weilDeligneParam_dual_listSum_absTwist_special E Ω A w h
  rw [e1, hl, hP, hT, hT, WD.lpTw_add]
  congr 2
  ring

private theorem map_summand_dual (H : CuspT a ha r) {l l' : List (Segment (w.adicCompletion E))}
    (hg : ∀ Δ ∈ l, GoodCusp Δ.first) (hF : List.Forall₂ SegDual l l') :
    l'.map (fun Δ => ((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)) =
      l.map (fun Δ => (((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).lpDual) := by
  induction hF with
  | nil => rfl
  | @cons Δ Δ' l l' hd _ ih =>
    rw [List.map_cons, List.map_cons, ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)),
      summand_dual H (hg _ List.mem_cons_self) hd]

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.extDual :
    UpperTheory.Zero.LLC.ExtDual := by
  intro E Ω _ _ _ _ _ A w h a ha r rc H hE n π π' hg hπ
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, h𝔪⟩ := UpperTheory.Zero.LLC.Pr.exh _ (cls π)
  have hL : IsL ((𝔪.toList : List _) : Multiset (Segment (w.adicCompletion E))) (cls π).rep := by
    rw [Multiset.coe_toList]; exact h𝔪
  obtain ⟨l', hF, hL'⟩ := (UpperTheory.Zero.LLC.Pr.dual (w.adicCompletion E)).2 𝔪.toList (cls π) (cls π') hL ⟨n, π, π', rfl, rfl, hπ⟩
  have hgl := ((UpperTheory.Zero.LLC.goodSeg (w.adicCompletion E)).1 _ _ hL).1 hg
  rw [hE _ _ hL, hE _ _ hL', segSum, segSum, (GlobalTheory.T.weilDeligneParam_dual_listSum_absTwist_special E Ω A w h).1, List.map_map]
  exact congrArg sumList (UpperTheory.Zero.LLC.map_summand_dual H hgl hF)
