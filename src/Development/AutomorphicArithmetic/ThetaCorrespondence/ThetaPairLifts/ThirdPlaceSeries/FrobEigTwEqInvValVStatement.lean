module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrobEigTwEqInvValV
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
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isSplit_at_good_heightOne_place_of_used0 : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {((GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂˣ) : ℂ)⁻¹} := by
  exact _root_.GlobalTheory.TieFrob.frobEig_tw_eq_inv_valV_alt
end
