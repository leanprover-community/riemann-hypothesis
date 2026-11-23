module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameKeepsMatricesSplitPlaceReductionLocal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead



theorem _root_.GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n), IdFrame hF P → ∀ (hn : V.rank = n) (κ : GAf D.host.E n), (κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔ Lev.finE V (P.ψ κ) ∈ St (1 : GL (Fin V.rank) (Lev.EAf D))) ∧ ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, κ ∈ ReciprocityTheory.Aut.Umax D.host.E n → ∀ a c : Fin V.rank, NX.locM s κ (Fin.cast hn a) (Fin.cast hn c) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) ∧ ∀ u : 𝓞 D.host.E, Valued.v (s.i (u : D.host.E) - NX.locM s κ (Fin.cast hn a) (Fin.cast hn c)) < 1 ↔ (redFn (1 : GL (Fin V.rank) (Lev.EAf D)) s.w (Lev.finE V (P.ψ κ))).val a c = Ideal.Quotient.mk s.w.asIdeal u := by
  first | exact @GlobalTheory.MtRead.Red.red_eq_local | exact GlobalTheory.MtRead.Red.red_eq_local | (intros; apply GlobalTheory.MtRead.Red.red_eq_local <;> assumption)
