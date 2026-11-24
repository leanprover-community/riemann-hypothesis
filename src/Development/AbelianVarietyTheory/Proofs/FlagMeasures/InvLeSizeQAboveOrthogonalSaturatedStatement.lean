module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvLeSizeQAboveOrthogonalSaturated
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
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets

@[expose] public section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

theorem _root_.GlobalTheory.T.inv_le_sizeQ_above_orthogonal_saturated : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → ∀ N, perpIn I x R < N → N ≤ lamX I x → hi⁻¹ ≤ sizeQ (bas I) (frm I x) N (perpIn I x R) := by
  first | exact @GlobalTheory.Count.PerpSize.inv_le_sizeQ_perp | exact GlobalTheory.Count.PerpSize.inv_le_sizeQ_perp | (intros; apply GlobalTheory.Count.PerpSize.inv_le_sizeQ_perp <;> assumption)
