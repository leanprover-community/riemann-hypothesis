module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRingHomPowerSeriesRoot
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


theorem _root_.GlobalTheory.T.exists_ringHom_powerSeries_root' : ∀ (O K : Type) [CommRing O] [CommRing K] (φ : PowerSeries O →+* K) (k : ℕ) (t : K), 0 < k → t ^ k = φ PowerSeries.X → ∃ Φ : PowerSeries O →+* K, (∀ a, Φ (PowerSeries.C a) = φ (PowerSeries.C a)) ∧ Φ PowerSeries.X = t ∧ ∀ f, Φ f ∈ Subring.closure (Set.range φ ∪ {t}) := by
  first | exact @GlobalTheory.exists_ringHom_powerSeries_root | exact GlobalTheory.exists_ringHom_powerSeries_root | (intros; apply GlobalTheory.exists_ringHom_powerSeries_root <;> assumption)
