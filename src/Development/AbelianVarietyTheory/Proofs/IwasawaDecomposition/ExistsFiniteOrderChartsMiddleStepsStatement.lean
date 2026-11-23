module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleSteps
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_finiteOrder_charts_middle_steps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → ∀ k : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i), GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i k → ∃ K : ∀ β : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)), I.Reads u a i (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i) (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1) (fun c s => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1 := by
  first | exact @GlobalTheory.Mem.Col2.ChExM.exists_charts | exact GlobalTheory.Mem.Col2.ChExM.exists_charts | (intros; apply GlobalTheory.Mem.Col2.ChExM.exists_charts <;> assumption)
