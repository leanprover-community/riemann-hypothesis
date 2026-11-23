module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcrossOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQ0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NewformAut0
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleResidualOfHyp
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr
open UpperTheory.GalN.V
theorem UpperTheory.V.Z.Win.A4.newAdmS_alt (P : _root_.UpperTheory.V.Af.Hypotheses') (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e M : ℕ)
    (he : 1 ≤ e) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hirr : IsIrr W)
    (hf : (∃ f : Newform (2 * e + 1), f.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ _root_.UpperTheory.V.Z.Win.WitAQ ι W)
    (hlev : Level l M ![(e : ℤ), -(e : ℤ)] W) (hcyc : IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W)) :
    _root_.UpperTheory.GalN.V.AdmRNAlt ι M ![(e : ℤ), -(e : ℤ)] 0 W := by
  obtain ⟨⟨f, hf⟩, hw⟩ := hf
  exact ⟨hirr, _root_.UpperTheory.GalN.V.isAutQA_of_isAutomorphicOverImagQuad_of_witAQ (_root_.UpperTheory.GalN.V.newformAut0_alt P (2 * e + 1) (by omega) f l Ω ι W _ hf) fun _ => hw, hlev, ⟨_, hcyc, dual_two W⟩,
    _root_.UpperTheory.V.Z.Win.A4.safeUGap' hlev fun i j => by fin_cases i <;> fin_cases j <;> simp <;> omega⟩
end
end
