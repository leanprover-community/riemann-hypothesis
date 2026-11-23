module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemZAndCuspOfSteps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.prvG6_of_admissible_of_g6_decomposition : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt → _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight' → _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation' → _root_.GlobalTheory.StringRepresentationDecomposition.MuCharacterCondition → EigenCharTwist → _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount → Numerics → Rest → ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → SumRepresentations.ConclusionG6 D := by
  first | exact @_root_.GlobalTheory.EigenPoint.prvG6_of_realisation_mu_res_count_numerics | exact _root_.GlobalTheory.EigenPoint.prvG6_of_realisation_mu_res_count_numerics | (intros; apply _root_.GlobalTheory.EigenPoint.prvG6_of_realisation_mu_res_count_numerics <;> assumption)
end
