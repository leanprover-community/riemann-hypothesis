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
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
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

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace GlobalTheory.RgGu

theorem rank_piTensor_le_one {h : ℕ} (M : Fin h → Type) [∀ a, AddCommGroup (M a)] [∀ a, Module ℂ (M a)]
    (hM : ∀ a, Module.rank ℂ (M a) ≤ 1) : Module.rank ℂ (⨂[ℂ] a, M a) ≤ 1 := by
  let b := fun a => Module.Free.chooseBasis ℂ (M a)
  have hs : ∀ a, Subsingleton (Module.Free.ChooseBasisIndex ℂ (M a)) := fun a =>
    Cardinal.le_one_iff_subsingleton.1 (by rw [(b a).mk_eq_rank'']; exact hM a)
  rw [← (Basis.piTensorProduct b).mk_eq_rank'', Cardinal.le_one_iff_subsingleton]
  infer_instance



theorem whitRankStd_of_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.WhitRankStd k := by
  intro k _ _ _ _ hW hI ψ hc h1 h N x hd
  have h2 : Module.rank ℂ (⨂[ℂ] a, TwJacquet (x a).rep (unipB k (Fin (x a).1)) (whitChar ψ (x a).1)) ≤ 1 :=
    rank_piTensor_le_one _ fun a => hI ψ hc h1 (x a).1 (x a).2.rep.V (x a).rep (x a).2.rep.smooth (x a).2.rep.irr
  obtain ⟨e⟩ := hW ψ hc h1 h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V) (fun a => (x a).rep)
    (fun a => (x a).2.rep.smooth)
  have h3 := e.rank_eq
  change Module.rank ℂ (TwJacquet (multiProd (stdBlocks (fun a => (x a).1) hd) (fun a => (x a).rep)) (unipB k (Fin N))
    (whitChar ψ N)) ≤ 1
  rw [h3]
  exact h2

end GlobalTheory.RgGu

end
