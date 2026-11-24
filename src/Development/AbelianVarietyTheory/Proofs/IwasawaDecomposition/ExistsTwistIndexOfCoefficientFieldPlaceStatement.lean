module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistIndexOfCoefficientFieldPlace
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_twistIndex_of_coefficientField_place : ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd)
    (Sp : RingSpec D cf b0 b1 Sx T) (w : D.what₂.places.Pl), ∃ i, T.l i = D.what₂.places.resChar w ∧
      ∀ x : D.LL0, 0 ≤ D.what₂.places.val w (x : D.what₂.LL) ↔
        T.emb0 i x ∈ (algebraMap (T.O0 i) (FractionRing (T.O0 i))).range := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.CoverPl.exists_setting_of_place | exact GlobalTheory.HeightCounting.FormsStep.CoverPl.exists_setting_of_place | (intros; apply GlobalTheory.HeightCounting.FormsStep.CoverPl.exists_setting_of_place <;> assumption)
