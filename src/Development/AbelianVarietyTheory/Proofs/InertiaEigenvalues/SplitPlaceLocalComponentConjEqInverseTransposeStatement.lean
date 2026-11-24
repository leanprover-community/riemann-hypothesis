module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLocalComponentConjEqInverseTranspose
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.splitPlaceLocalComponent_conj_eq_inverseTranspose : ∀ (D : D7) (n : ℕ) (π : NG.AutRep D.host.E n) (s : SplitPlace D.host.E)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion D.host.E))), IsLocS π.S s σ →
    ∃ (κ : s.w.adicCompletion D.host.E ≃+* (GlobalTheory.TypeTame.conjSP s).w.adicCompletion D.host.E)
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).w.adicCompletion D.host.E))) (e : σ.V ≃ₗ[ℂ] σ'.V),
      Continuous κ ∧ (∀ x : D.host.E, κ (algebraMap D.host.E _ x) = algebraMap D.host.E _ (D.host.conj x)) ∧
      IsLocS π.S (GlobalTheory.TypeTame.conjSP s) σ' ∧
      ∀ g a, e (σ.ρ (GlobalTheory.TypeTame.invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a) := by
  first | exact @GlobalTheory.ConjLocComp.exists_isLocS_conjSP | exact GlobalTheory.ConjLocComp.exists_isLocS_conjSP | (intros; apply GlobalTheory.ConjLocComp.exists_isLocS_conjSP <;> assumption)
