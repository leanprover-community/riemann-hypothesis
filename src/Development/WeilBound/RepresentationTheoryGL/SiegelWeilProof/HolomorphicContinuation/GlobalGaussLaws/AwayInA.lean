module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
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

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct SchwartzMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

variable {D : D7} {n : ℕ}

theorem evalPoly_congr {m : ℕ} (p : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) (τ : D.what₂.Tau)
    (hp : ∀ v ∈ p.vars, v.1 ≠ τ) (z z' : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (h : ∀ τ', τ' ≠ τ → z τ' = z' τ') :
    evalPoly p z = evalPoly p z' := by
  unfold evalPoly
  change MvPolynomial.eval₂ (RingHom.id ℂ) _ p = MvPolynomial.eval₂ (RingHom.id ℂ) _ p
  apply MvPolynomial.eval₂_congr
  intro i c hi hc
  have hv : i ∈ p.vars := (MvPolynomial.mem_vars_iff_mem_support i).2 ⟨c, (MvPolynomial.mem_support_iff).2 hc, hi⟩
  have e := h i.1 (hp i hv)
  simp only [e]

theorem gAway_congr (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (z z' : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) (h : ∀ τ', τ' ≠ τ → z τ' = z' τ') :
    gAway V l s τ z = gAway V l s τ z' := by
  classical
  unfold gAway
  congr 2
  refine Finset.sum_congr rfl (fun τ' hτ' => ?_)
  rw [h τ' (Finset.mem_filter.1 hτ').2]

theorem dep (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) {Ψ : Mx D V.rank n → ℂ} (hΨ : Ψ ∈ awayA θ V n l s τ) (x x' : Mx D V.rank n)
    (hx : ∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') (hf : x.map (finPart D) = x'.map (finPart D)) :
    Ψ x = Ψ x' := by
  induction hΨ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨p, g, _, hp, rfl⟩ := hφ
    simp only
    have hf' : (fun i j => finPart D (x i j)) = (fun i j => finPart D (x' i j)) := hf
    rw [evalPoly_congr p τ hp _ _ hx, gAway_congr V l s τ _ _ hx, hf']
  | zero => rfl
  | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb]
  | smul c a _ ha => simp only [Pi.smul_apply, ha]

end PositivityTheory.Rg.Sw.Glob.AwayPf
