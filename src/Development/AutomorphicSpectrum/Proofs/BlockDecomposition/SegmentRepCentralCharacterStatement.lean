module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacter
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

theorem _root_.GlobalTheory.T.segment_rep_central_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (y : IrrGL (k := k)), IsLSeg Δ y.rep → ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy Δ.first t c → Zl.ScalarBy y t (c ^ Δ.len * ((absPow k (((Δ.len * (Δ.len - 1) / 2 : ℕ) : ℂ)) (t ^ Δ.d) : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.ZlScalar.scalarBy_lseg | exact GlobalTheory.CompanionTheory.ZlScalar.scalarBy_lseg | (intros; apply GlobalTheory.CompanionTheory.ZlScalar.scalarBy_lseg <;> assumption)
