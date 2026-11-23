module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRecordCgTrueT
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfCharOfCharOfHasInfQ

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocGL GlobalTheory.HeightCounting GlobalTheory.HeightCounting.TrueSide UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
section Twist
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} [_root_.NumberField.IsTotallyComplex E]
  (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
include hF in
theorem locPar_twist_alt (π : CG E a) (χ : HChar E) (h : IsPlaceOver A w)
    (hg : Good (⟨a, ParLaws.toCl (π.loc w)⟩ : IrrGL (k := w.adicCompletion E))) :
    _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (π.twist χ) h = (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL π h).lpChar (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ) h) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity, _root_.GlobalTheory.CuspRep.ParLawsT.locParT, _root_.GlobalTheory.CuspRep.ParLawsT.locParT, cls_loc_twist]
  have _ := hF
  exact _root_.UpperTheory.One.M.LawsM.twist H _ _ _ hg
end Twist
namespace Old
end Old
namespace New
end New
end UpperTheory.One.M
end
end
