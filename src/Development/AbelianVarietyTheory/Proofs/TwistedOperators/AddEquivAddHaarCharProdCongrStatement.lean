module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharProdCongr
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

theorem _root_.GlobalTheory.T.addEquivAddHaarChar_prodCongr : ∀ (G₁ G₂ : Type) [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂] (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂), addEquivAddHaarChar (prodCE e₁ e₂) = addEquivAddHaarChar e₁ * addEquivAddHaarChar e₂ := by
  first | exact @GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE | exact GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE | (intros; apply GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE <;> assumption)
