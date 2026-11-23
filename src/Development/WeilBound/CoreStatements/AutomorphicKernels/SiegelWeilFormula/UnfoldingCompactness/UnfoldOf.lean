module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IsClosedSiegelStabiliser
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.UnfoldCore
import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.kunf

theorem unfold : Unfold := by
  intro F E _ _ _ _ _ σ d s₁ f hf hE
  obtain ⟨U, p, Ê, t, -, -, -, -, -, -, -, hmaj⟩ := hE 0
  refine ⟨t, fun z hz nb lam 𝓖 hc ε w hw x => ?_⟩
  have hΦ : (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) = flat d.a f s₁ z := funext fun x => by
    rw [flat, ht_eq]
  have hmaj' := (hmaj z hz).1
  rw [hΦ] at hmaj'
  have hlaw : Law d.χ (s₁ + d.n / 2) f := hf.law
  have hlawF := hlaw.flat (s₀ := s₁) d.ok.hgt (a_pos d) z
  have hcore := unfoldCore d.B d.ok.good d.ok.frame hc (flat d.a f s₁ z)
    (continuous_flat hf.cont (continuous_a d) (a_pos d) z)
    (fun p hp hpr y => hlawF.rat d.ok.hecke hp hpr y)
    (fun p t ht hdet y => by rw [hlawF p t y ht, hdet]; simp)
    hmaj' hw x
  refine ⟨hcore.1, fun T hT => ?_⟩
  show fc d.B.ψ d.b nb lam 𝓖 (GlobalTheory.Eis.cosetSum _ _ (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x)) T x = _
  rw [hΦ]
  exact hcore.2 T hT

end PositivityTheory.SiegelWeilFormula.kunf

end
