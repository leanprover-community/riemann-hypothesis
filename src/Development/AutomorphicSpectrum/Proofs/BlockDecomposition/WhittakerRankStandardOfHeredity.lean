module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZSeg

theorem rank_piTensorProduct_le_one {ι : Type} [Fintype ι] (W : ι → Type) [∀ a, AddCommGroup (W a)]
    [∀ a, Module ℂ (W a)] (hW : ∀ a, Module.rank ℂ (W a) ≤ 1) : Module.rank ℂ (⨂[ℂ] a, W a) ≤ 1 := by
  classical
  choose w hw using fun a => rank_le_one_iff.1 (hW a)
  refine rank_le_one_iff.2 ⟨PiTensorProduct.tprod ℂ w, fun t => ?_⟩
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    choose c hc using fun a => hw a (f a)
    refine ⟨r * ∏ a, c a, ?_⟩
    have hf : f = fun a => c a • w a := funext fun a => (hc a).symm
    rw [hf, (PiTensorProduct.tprod ℂ).map_smul_univ, smul_smul]
    simp only [RingHom.id_apply]
  | add x y hx hy =>
    obtain ⟨r, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    exact ⟨r + s, add_smul _ _ _⟩

theorem whitRank_multiProd_le_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hH : GlobalTheory.BZMir.Leib.WhitHeredity k) (ψ : AddChar k Circle) (hc : Continuous ψ)
    (h1 : ψ ≠ 1) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (hs : ∀ a, IsSmooth (π a))
    (hr : ∀ a, Module.rank ℂ (TwJacquet (π a) (unipB k (Fin (d a))) (whitChar ψ (d a))) ≤ 1) :
    Module.rank ℂ (TwJacquet (multiProd (stdBlocks d hd) π) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  obtain ⟨e⟩ := hH ψ hc h1 h N d hd X π hs
  exact e.rank_eq.le.trans (rank_piTensorProduct_le_one _ hr)

theorem whitRankStd_of_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k →
    GlobalTheory.BZSeg.WhitRankStd k := by
  intro k _ _ _ _ hH hR ψ hc h1 h N x hd
  exact whitRank_multiProd_le_one hH ψ hc h1 h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V) (fun a => (x a).rep)
    (fun a => (x a).2.rep.smooth)
    (fun a => hR ψ hc h1 (x a).1 (x a).2.rep.V (x a).rep (x a).2.rep.smooth (x a).2.rep.irr)

end GlobalTheory.CompanionTheory.BZSeg

end
