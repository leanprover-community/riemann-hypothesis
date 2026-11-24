module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentLtOfPrecedes
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

theorem _root_.GlobalTheory.T.exponent_lt_of_precedes_of_isLSeg : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ Δ' : Segment k) (y y' : IrrGL (k := k)) (s s' : ℝ), IsLSeg Δ y.rep → IsLSeg Δ' y'.rep → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y t c → ‖c‖ = nabs k t ^ ((y.1 : ℝ) * s)) → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y' t c → ‖c‖ = nabs k t ^ ((y'.1 : ℝ) * s')) → Δ.Precedes Δ' → s < s' := by
  first | exact @GlobalTheory.CompanionTheory.SegExp.exponent_lt_of_precedes | exact GlobalTheory.CompanionTheory.SegExp.exponent_lt_of_precedes | (intros; apply GlobalTheory.CompanionTheory.SegExp.exponent_lt_of_precedes <;> assumption)
