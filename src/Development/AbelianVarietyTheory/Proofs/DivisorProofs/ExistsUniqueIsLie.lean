module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEvDefectDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefectCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLieOfAdditive
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem QLog.Chart.existsUnique_isLie : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → ∃! l : G.dual.Lie, c.IsLie f l := by
  intro p _ O E _ _ _ hF G d c f hf
  haveI : IsAdicComplete (Ideal.span {(p : O)}) O := hF.complete
  have hinj : Function.Injective (MvPowerSeries.map (σ := Fin d) (algebraMap O E)) := by
    intro s t h
    ext α
    have := congrArg (MvPowerSeries.coeff α) h
    simp only [MvPowerSeries.coeff_map] at this
    exact hF.inj this
  obtain ⟨hex, hcomp⟩ := GlobalTheory.QLog.defect_compat p O E hF G d c f hf
  choose s hs _ using fun n : ℕ => hex (p ^ n)
  have hadd := GlobalTheory.QLog.cobOne_ev_defect_dvd p O E hF G d c f hf
  obtain ⟨l, hl, huniq⟩ := GlobalTheory.LieOfAdditive.existsUnique_lie_of_additive p O G (fun n => c.ev n (s n))
    (fun n => hadd n (s n) (hs n)) (fun n => hcomp n (s n) (s (n + 1)) (hs n) (hs (n + 1)))
  refine ⟨l, ⟨fun n => In.top_iff.2 ⟨s n, hs n⟩, ?_⟩, ?_⟩
  · intro n w φ t hφ ht
    have : t = s n := hinj (ht.trans (hs n).symm)
    subst this
    exact hl n w φ hφ
  · intro l' hl'
    exact huniq l' fun n w φ hφ => hl'.2 n w φ (s n) hφ (hs n)

end GlobalTheory
