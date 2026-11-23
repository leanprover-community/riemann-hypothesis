module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentification
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizationEqOfHeckeAgreementTwistLawsStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
noncomputable section
namespace GlobalTheory.LocCoincide


theorem built_laws_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D →
    GlobalTheory.RowTie.CharLaws D.nd D.naut ∧
    (∀ (i i' : D.nd.Loc) (σ : D.what₂.FT) (v : PlE D.host), IsSplitPl D.host v → D.naut.locW i σ v = D.naut.locW i' σ v) ∧
    (∀ i i' : D.nd.Loc, D.nd.j i = D.nd.j i' → D.nd.w i = D.nd.w i' → D.naut.muC i = D.naut.muC i') := by
  intro hL D b
  obtain ⟨D0, cf, jE, A, cg, au, rep, row, low, Pq, S, hLm, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩ := b
  subst eq
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.RowLaws.main _ _ _ _ _ A.wdT).2.1
  · intro i i' σ v _
    exact (Au.locW i σ v).trans (Au.locW i' σ v).symm
  · intro i i' hj hw
    have hj' : L.X.nd.j i = L.X.nd.j i' := hj
    have hw' : L.X.nd.w i = L.X.nd.w i' := hw
    have hjr : 1 ≤ L.X.nd.j i ∧ L.X.nd.j i ≤ D0.R.m := L.X.nd.j_range i
    have hmu : L.X.nd.mu i = L.X.nd.mu i' :=
      (L.X.nd.mu_w i).trans ((congrArg _ hw').trans (L.X.nd.mu_w i').symm)
    have e1 : L.X.nd.j i - 1 + 1 = L.X.nd.j i := by omega
    have e2 : L.X.nd.j i - 1 + 1 = L.X.nd.j i' := by omega
    have h1 := Au.muC i ⟨L.X.nd.j i - 1, by omega⟩ e1
    have h2 := Au.muC i' ⟨L.X.nd.j i - 1, by omega⟩ e2
    show L.Y.muC i = L.Y.muC i'
    apply A.chr.e1.injective
    apply Subtype.ext
    exact h1.trans ((congrArg (fun μ => tp.tup μ ⟨L.X.nd.j i - 1, by omega⟩) hmu).trans h2.symm)
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (M : Formalism.L2.MtFam D), _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D →
    Formalism.L2.HeckeTied D M → KillingConditions.LocalisationUniqueness D := fun hL D M b hT =>
  have h := _root_.GlobalTheory.LocCoincide.built_laws_alt hL D b
  GlobalTheory.T.localization_eq_of_heckeAgreement_twistLaws D M hT h.1 h.2.1 h.2.2
end GlobalTheory.LocCoincide
end
end
