module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.BlockOrderedSquareIntegrable
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.HolDS

variable {p q : ℕ}

instance t2Space_cuspAdeles (T : GrpData p q) : T2Space T.G := T.emb.t2Space

instance instSecondCountable (T : GrpData p q) : SecondCountableTopology T.G := by
  haveI : SecondCountableTopology (Mat p q) := inferInstanceAs (SecondCountableTopology (Ix p q → Ix p q → ℂ))
  haveI : SecondCountableTopology (Mat p q)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Ix p q) ℂ) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  exact T.emb.secondCountableTopology

instance instLocallyCompact (T : GrpData p q) : LocallyCompactSpace T.G := by
  haveI : LocallyCompactSpace (Mat p q) := inferInstanceAs (LocallyCompactSpace (Ix p q → Ix p q → ℂ))
  exact (GlobalTheory.RealPar.SqInt.isClosedEmbedding_emb T).locallyCompactSpace

end GlobalTheory.HolDS

end
