module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductRankLeOneStatement
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
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RgGu

theorem rank_twJacquet_multiProd_le_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hH : GlobalTheory.BZMir.Leib.WhitHeredity k) (ψ : AddChar k Circle) (hc : Continuous ψ)
    (h1 : ψ ≠ 1) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (hs : ∀ a, IsSmooth (π a))
    (hr : ∀ a, Module.rank ℂ (TwJacquet (π a) (unipB k (Fin (d a))) (whitChar ψ (d a))) ≤ 1) :
    Module.rank ℂ (TwJacquet (multiProd (stdBlocks d hd) π) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  obtain ⟨e⟩ := hH ψ hc h1 h N d hd X π hs
  exact e.rank_eq.le.trans (GlobalTheory.T.tensor_product_rank_le_one _ hr)

theorem rank_twJacquet_prodIrr_le_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k →
    ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k))
      (hd : ∑ a, (x a).1 = N),
      Module.rank ℂ (TwJacquet (prodIrr x hd) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  intro k _ _ _ _ hH hR ψ hc h1 h N x hd
  exact rank_twJacquet_multiProd_le_one hH ψ hc h1 h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V)
    (fun a => (x a).rep) (fun a => (x a).2.rep.smooth)
    (fun a => hR ψ hc h1 (x a).1 (x a).2.rep.V (x a).rep (x a).2.rep.smooth (x a).2.rep.irr)

end GlobalTheory.CompanionTheory.RgGu

end
