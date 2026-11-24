module

public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundOverSecondEmbeddingAnyBasePoint
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.orbitBound_overSecondEmbedding_anyBasePoint : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D) (C6 C : ℝ), OrbitPlaces.OrbitLetterBoundsAll C6 C → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge C6 C K ce → ∀ (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p), IsResidueClassZero D p → hP D p ≠ 0 → (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ u, ∀ i < D.R.m, ∀ (t : HH D) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 → (sg = 1 ∨ sg = -1) → product_zeroth_first_parts.B1 p (nP D p) be → product_zeroth_first_parts.B2 p (nP D p) be → product_zeroth_first_parts.B3 p (nP D p) be → product_zeroth_first_parts.B4 p (nP D p) be → OrbitPlaces.OrbGe E p h u i (true, t) ep sg be (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  first | exact @GlobalTheory.TwU.orbitBound_overSecondEmbedding_anyBasePoint_alt | exact GlobalTheory.TwU.orbitBound_overSecondEmbedding_anyBasePoint_alt | (intros; apply GlobalTheory.TwU.orbitBound_overSecondEmbedding_anyBasePoint_alt <;> assumption)
