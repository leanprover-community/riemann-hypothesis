module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibreFieldPointsCardLEDiagonalComplementSecondPr
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.fibreFieldPointsCardLE_diagonalComplementSecondProjection : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (n : ℕ), GlobalTheory.EtC.Tr.FibrePointsLE f (n + 1) → GlobalTheory.EtC.Tr.FibrePointsLE (GlobalTheory.EtC.Tr.diagComplHom f) n := by
  first | (exact @GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom) | (exact GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom) | (intros; apply GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom  <;> assumption)
