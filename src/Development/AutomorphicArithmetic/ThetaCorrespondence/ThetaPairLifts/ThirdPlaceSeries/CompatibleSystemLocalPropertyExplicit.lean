module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace GlobalTheory.SerSys.Assembly
abbrev _root_.GlobalTheory.SerSys.Assembly.CompatibleSystemLocalPropertyExplicitAlt : Prop :=  _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → Green → GlobalTheory.Published.ZelevinskyPolynomialRing →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L →
    (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k),
      TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) →
    GlobalTheory.HeightCounting.Up.CenLoc D P.M → GlobalTheory.TypeLeaf.SerLoc D
end GlobalTheory.SerSys.Assembly
end
end
