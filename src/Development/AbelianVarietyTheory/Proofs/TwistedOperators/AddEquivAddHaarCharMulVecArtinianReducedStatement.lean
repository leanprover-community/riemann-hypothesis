module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharMulVecArtinianReduced
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

theorem _root_.GlobalTheory.T.addEquivAddHaarChar_mulVec_artinian_reduced : ∀ (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [LocallyCompactSpace B] [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B], IsArtinianRing B → IsReduced B → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [MeasurableSpace (κ → B)] [BorelSpace (κ → B)] (M : Matrix κ κ B) (hM : IsUnit M.det), addEquivAddHaarChar (mulVecCE M hM) = modu B M.det := by
  first | exact @GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE | exact GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE | (intros; apply GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE <;> assumption)
