module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.splitIdempotent_prime_projection_correspondence : ∀ (D : D7), (∀ (e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∃ (v : FinPl D) (φ : SplitProj D v), IsIdemOf φ e ∧ IsProjAt φ PP) ∧ ∀ (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E), IsProjAt φ PP → PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal ∧ (∀ PP', IsProjAt φ PP' → PP' = PP) ∧ ∀ e, IsIdemOf φ e → Formalism.L2.NTheta.IsIdemAt e PP ∧ (∀ e', Formalism.L2.NTheta.IsIdemAt e' PP → e' = e) ∧ ∀ φ' : SplitProj D v, IsIdemOf φ' e → φ' = φ := by
  first | exact @GlobalTheory.SplitIdemDict.idem_dictionary | exact GlobalTheory.SplitIdemDict.idem_dictionary | (intros; apply GlobalTheory.SplitIdemDict.idem_dictionary <;> assumption)
