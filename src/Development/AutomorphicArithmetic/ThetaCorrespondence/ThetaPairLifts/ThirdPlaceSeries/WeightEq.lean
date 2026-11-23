module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
public import Development.WeilBound.CoreStatements.AutomorphicKernels.TemperedUnitNorm.NormEqOneOfTemperedRec
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FillPreservesIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section



section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.WeilDeligne NumberField IsDedekindDomain Polynomial
end GlobalTheory.HeightCounting
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GalAllPlaces
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.WeilDeligne Polynomial
end GlobalTheory.GalAllPlaces
end
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.CsdTwistGal
end GlobalTheory.CsdTwistGal
namespace GlobalTheory.TempSatGal
theorem weight_eq_alt_alt {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {a : ℕ} (ha : 1 ≤ a) {π : CuspSub E a} {χ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}
    (H : _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT) (m : (E →+* ℂ) → Multiset ℂ) (s : ℝ)
    (hcard : ∀ τ, (m τ).card = a) (hinf : ∀ τ, (CG.mk π).infChar τ = (m τ).map (· + (s : ℂ)))
    (hconj : ∀ τ, m (ComplexEmbedding.conjugate τ) = (m τ).map Neg.neg) :
    (wt : ℝ) = (a : ℝ) - 1 - 2 * s := by
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτ : ι.toRingHom.comp (ι.symm.toRingHom.comp τ0) = τ0 := by ext x; simp
  set τ : E →+* Qbar l := ι.symm.toRingHom.comp τ0 with hτdef
  set X : Multiset ℂ := (HT τ).map (fun n : ℤ => (n : ℂ)) with hXdef
  have hX : X = (m τ0).map (fun z => (((a : ℂ) - 1) / 2 - s) + (-1) * z) := by
    rw [hXdef, H.weights τ, hτ, hinf, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]; ring
  have hY : (HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom)).map (fun n : ℤ => (n : ℂ)) =
      X.map (fun z => (wt : ℂ) + (-1) * z) := by
    rw [H.weights_conj, hXdef, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun n _ => ?_
    simp only [Function.comp_apply]; push_cast; ring
  have hZ : (HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom)).map (fun n : ℤ => (n : ℂ)) =
      (m τ0).map (fun z => (((a : ℂ) - 1) / 2 - s) + 1 * z) := by
    rw [H.weights, comp_complexConj, hτ, hinf, hconj, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]; ring
  have hcX : (X.card : ℂ) = a := by rw [hX, Multiset.card_map, hcard]
  have e := congrArg Multiset.sum (hY.symm.trans hZ)
  rw [sum_map_affine, sum_map_affine, hcX, hX, sum_map_affine, hcard] at e
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have h : (wt : ℂ) = (a : ℂ) - 1 - 2 * (s : ℂ) := by
    apply mul_left_cancel₀ ha0
    linear_combination e
  exact_mod_cast h
end GlobalTheory.TempSatGal
end
end
end
