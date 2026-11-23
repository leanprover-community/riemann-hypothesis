module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPullbackTeichmullerLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.quasiLogarithm_pullback_teichmullerLift : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d e : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (hμ : IsLaw μ) (hν : IsLaw ν) (φ : Fin e → MvPowerSeries (Fin d) k), IsHom μ ν φ → ∀ f ∈ quasiLog p hν, subst (fun j => Katz.lift p (φ j)) f ∈ quasiLog p hμ ∧ (∀ c, Red p (cob1 (fun j => Katz.lift p (ν j)) f) c → Red p (cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f)) (pull2 φ c)) ∧ ∀ w, RedV p (lin f) w → RedV p (lin (subst (fun j => Katz.lift p (φ j)) f)) (pullLin φ w) := by
  first | exact @GlobalTheory.KatzPull.quasiLog_pull | exact GlobalTheory.KatzPull.quasiLog_pull | (intros; apply GlobalTheory.KatzPull.quasiLog_pull <;> assumption)
