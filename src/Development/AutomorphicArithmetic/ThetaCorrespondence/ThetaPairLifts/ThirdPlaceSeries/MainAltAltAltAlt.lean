module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstCharacterTrivialWildInertiaTypePrimeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointParOfTwist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistInvOfCharLawsMultOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleBranchingIffIsBranching
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TameAnyAtOfIsConjPl
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameSumOfInputs
public import Development.DiscreteGroups.GlobalIrreducibility.DzBigDef
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section



section
noncomputable section
namespace GlobalTheory.IneAway
open GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.IneAway
namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels
end GlobalTheory.TypeLeaf
namespace GlobalTheory.TypeLeaf.ConjPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open scoped Pointwise
end GlobalTheory.TypeLeaf.ConjPlace
namespace GlobalTheory.AdmTame
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
theorem main_alt_alt_alt : ∀ D : D7, SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → UpperTheory.GalS.LabTameS D.nd D.naut → UpperTheory.GalS.AdmissibleResidualTameEigenvalues D := by
  intro D h0 hG hA hL
  obtain ⟨hLP, hAut, -⟩ := h0
  have hW : GlobalTheory.TypeLeaf.WildOne D := hL.1
  have hGal : _root_.UpperTheory.GalS.GalAwayN D := _root_.GlobalTheory.AdmTame.galAwayOfS' hG
  have hF : GlobalTheory.TypeLeaf.FrobDense D := by
    intro T hT
    rw [dense_iff_closure_eq]
    exact hA.2.2.1 T hT
  have hCL : GlobalTheory.TypeLeaf.CharLaws D := by
    intro w a χ χ' hχ hχ'
    obtain ⟨-, -, -, h4, h5, -⟩ := hLP w a a χ χ' 0 hχ hχ'
    exact ⟨h4, h5⟩
  have hM : GlobalTheory.TypeLeaf.MultOne D := by
    intro a π π' ha h
    have hp := hA.1 [⟨a, π, 1⟩] [⟨a, π', 1⟩] (by simp [ha]) (by simp [ha])
      (Filter.Eventually.of_forall fun w => by simp [isoLoc, spehLoc, h w])
    rw [List.singleton_perm_singleton] at hp
    simp only [Formalism.BasicNotions.Part.mk.injEq, heq_eq_eq, true_and] at hp
    exact hp.1
  have hT : GlobalTheory.TypeLeaf.TwistInv D := GlobalTheory.TypeLeaf.twistInv_of_charLaws_multOne D hCL hM
  have hz : ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG D.naut.etaTinv τ,
      ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ) := by
    intro τ z hz
    obtain ⟨m, hm⟩ := D.R.t_odd
    obtain ⟨h1, h2⟩ := hAut.2.1 τ
    rw [h2] at hz
    rcases h1 with h1 | h1 <;> rw [h1] at hz <;> simp at hz <;> subst hz
    · refine ⟨-(m : ℤ) - 1, ?_⟩
      rw [hm]; push_cast; ring
    · refine ⟨-(m : ℤ), ?_⟩
      rw [hm]; push_cast; ring
  have hP : GlobalTheory.TypeLeaf.PointPar D := GlobalTheory.TypeLeaf.pointPar_of_twist D hT hAut.1.1 hz
  intro i Sig hx hf hsq hc ρ hρ
  exact _root_.GlobalTheory.TypeLeaf.tameSum_of_inputs_alt D hW (GlobalTheory.T.firstCharacter_trivial_wildInertia_typePrime D) hGal hF hP i Sig hx
    (_root_.UpperTheory.GalS.fullLabS_of_fullLabS_trivial ⟨hf, fun k v => hL.2 k v _ (hf k v) (hsq k v) (DiscreteGroups.sglob.DzType.big_of_le_nV D k (by
      obtain ⟨π, rfl⟩ := hc
      rw [GlobalTheory.InertialTypesCmp.lpDim_isoLoc]
      simp [rankIso, Ranks.nV]))⟩) hc ρ hρ
end GlobalTheory.AdmTame
end
end
