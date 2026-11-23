module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LiftFactorization.RamLiftOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatFamOfIsDiscrete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.NormRam
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
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.GalCut GlobalTheory.RealGal GlobalTheory.UnitaryBC UpperTheory.V.Published UpperTheory.Gal.UnramifiedFromSplittingCriterion UpperTheory.ConvolutionTheory.Sph

theorem UpperTheory.Gal.AbelianGaloisNormality.strongOf :
    UpperTheory.Gal.AbelianGaloisNormality.StrongOf := by
  intro hL hR K M _ _ _ _ _ _ _ _ hp a ha π hη
  have hno : ∀ η : HChar K, IsNormChar M η → (CG.mk π).twist η ≠ CG.mk π := by
    intro η hn he
    refine hη η hn ?_
    have h1 := (GlobalTheory.ResW.exists_satFam_of_isDiscrete K a).1 π
    have h2 : ∀ᶠ v in Filter.cofinite, η.UnrAt v :=
      Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified η)
    filter_upwards [h1, h2] with v hv hu
    obtain ⟨B, hB⟩ := hv
    refine ⟨hu, B, hB, ?_⟩
    have h3 := CG.HasSat.twist hB hu
    rw [he] at h3
    exact CG.HasSat.unique h3 hB
  obtain ⟨P, hP⟩ := hL K M hp a ha π hno
  refine ⟨P, ?_⟩
  refine ⟨fun w f B hf hB => ?_, hP.inf, hP.loc⟩
  by_cases hu : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal
  · exact hP.sat w f B hu hf hB
  · have h1 : (CG.mk P).HasSat w B := hR K M hp a ha π P hP.weak w hu B hB
    have h2 := (UpperTheory.ConvolutionTheory.Sph.normRam K M hp w hu).1
    have h3 : 2 ≤ normV (w.under (𝓞 K)) := GlobalTheory.WeilDeligne.one_lt_normV _
    have h4 : f = 1 := Nat.pow_right_injective h3 (by simpa [← h2] using hf.symm)
    subst h4
    simpa using h1
