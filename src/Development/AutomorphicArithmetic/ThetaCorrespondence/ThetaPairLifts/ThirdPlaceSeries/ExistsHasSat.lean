module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHasSatakeOfUnr
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

@[expose] public section



section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Satake
open GlobalTheory.LFun GlobalTheory.PRep GlobalTheory.CuspRep Formalism.UG
variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
variable [_root_.NumberField.IsTotallyComplex E]
end Satake
section Local
open GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}
variable [_root_.NumberField.IsTotallyComplex E] (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
include hF in
theorem exists_satake_frobenius_eigenvalues_eq_inv_of_unramified (π : CG E a) (h : IsPlaceOver A w) (hu : (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).unr) :
    ∃ B : Multiset ℂˣ, π.HasSat w B ∧ (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).frobEig = B.map fun b => ((b⁻¹ : ℂˣ) : ℂ) := by
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  have e : _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (Quotient.mk _ π) h = _ := _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ h
  rw [e] at hu
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) hu
  refine ⟨Finset.univ.val.map α, hasSatGL_locRep hσ (GlobalTheory.LFun.SatCompare.hasSatGL_of_hasSatakeGL
    ((GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ _ _).2 ⟨α, rfl, hα⟩)), ?_⟩
  rw [e, _root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) hα, WD.frobEig_diag, Multiset.map_map]
  rfl
end Local
section Polar
end Polar
section Record
end Record
section True
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
end GlobalTheory.HeightCounting
end
end
