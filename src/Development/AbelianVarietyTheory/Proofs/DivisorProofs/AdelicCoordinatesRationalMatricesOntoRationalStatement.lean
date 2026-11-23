module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCoordinatesRationalMatricesOntoRational
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)
open GlobalTheory.ThetaTransform

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.adelicCoordinates_rationalMatrices_onto_rational : ∀ (D : D7) (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AE D) ≃ₗ[AF D.host.F] VA D.host.F N), (∀ x : Matrix (Fin m) (Fin n) D.host.E, ∃ y z : Fin N → D.host.F, e (incM D.host.F x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) → ∀ y z : Fin N → D.host.F, ∃ x : Matrix (Fin m) (Fin n) D.host.E, e (incM D.host.F x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := by
  first | exact @GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps | exact GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps | (intros; apply GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps <;> assumption)
