module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionExteriorProductAssocComm
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

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm : ∀ (g : ℕ) [Fact g.Prime] (a b c n : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (γ : Gn g c → ℂ), IsClass α → IsClass β → IsClass γ → (n = a + b + c → hc (a + b) c (hc a b α β (a + b)) γ n = hc a (b + c) α (hc b c β γ (b + c)) n) ∧ (n = a + b → hc a b α β n = hc b a β α n) ∧ (hc 0 a (fun _ => 1) α a = α ∧ hc a 0 α (fun _ => 1) a = α) := by
  first | exact @GlobalTheory.GLq.HcRing.main | exact GlobalTheory.GLq.HcRing.main | (intros; apply GlobalTheory.GLq.HcRing.main <;> assumption)
