module

public import Formalism.SatakeDualWeyl.StatementF
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsMulMinusculeTopTerm
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.elementaryDivisors_mul_minuscule_top_term : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (n : ℕ), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → ∀ (d : Fin n → ℕ) (k : ℕ), Antitone d → (∀ i : Fin n, 0 < d i ↔ (i : ℕ) < k) → ∀ (g a : GL (Fin n) L), (∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ((k₁ * g * k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => ϖ ^ (d i - 1)) → (∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ((k₁ * a * k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i : Fin n => if (i : ℕ) < k then ϖ else 1) → ∀ d' : Fin n → ℕ, Antitone d' → (∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ((k₁ * (g * a) * k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => ϖ ^ d' i) → d' = d ∨ (∑ i, d' i = ∑ i, d i ∧ ∑ i, d' i ^ 2 < ∑ i, d i ^ 2) := by
  first | exact @GlobalTheory.Hk3.MinuscTop.elemDiv_mul_minuscule | exact GlobalTheory.Hk3.MinuscTop.elemDiv_mul_minuscule | (intros; apply GlobalTheory.Hk3.MinuscTop.elemDiv_mul_minuscule <;> assumption)
