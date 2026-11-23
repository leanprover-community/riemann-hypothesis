module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstLiftXPowFrob
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapFormalGroupLawQuasiLogarithms
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

theorem _root_.GlobalTheory.T.map_formalGroupLawQuasiLogarithms : ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [Field k'] [CharP k' p] (σ : k →+* k') (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (hμ : IsLaw μ) (hμ' : IsLaw (fun i => MvPowerSeries.map σ (μ i))), ∀ f ∈ quasiLog p hμ, MvPowerSeries.map (frMap p σ) f ∈ quasiLog p hμ' ∧ (f ∈ intBy p k (Fin d) 1 → MvPowerSeries.map (frMap p σ) f ∈ intBy p k' (Fin d) 1) ∧ (∀ t, Red p (cob1 (fun i => Katz.lift p (μ i)) f) t → Red p (cob1 (fun i => Katz.lift p (MvPowerSeries.map σ (μ i))) (MvPowerSeries.map (frMap p σ) f)) (MvPowerSeries.map σ t)) ∧ ∀ w, RedV p (lin f) w → RedV p (lin (MvPowerSeries.map (frMap p σ) f)) (fun i => σ (w i)) := by
  first | exact @GlobalTheory.Katz.quasiLog_map | exact GlobalTheory.Katz.quasiLog_map | (intros; apply GlobalTheory.Katz.quasiLog_map <;> assumption)
