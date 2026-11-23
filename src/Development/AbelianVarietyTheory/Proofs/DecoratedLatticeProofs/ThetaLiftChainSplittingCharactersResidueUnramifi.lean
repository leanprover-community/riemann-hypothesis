module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharTameAtOfFactorsThroughResidueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HatCPhiHat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypeResidueCharsUnramifiedTuple
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterEquivalenceLocalData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueCharStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfHeckeCharUnramifiStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

open GlobalTheory.StepLaw


open Classical in
theorem levRes_step : ∀ (D : D7) (c : Com D), c.Is → ∀ k < D.R.m, (∀ PP ∈ c.Pg, GlobalTheory.StepLaw.ResAt (c.chS (k + 1)) PP (c.chi (k + 1) PP)⁻¹ ∧ GlobalTheory.StepLaw.ResAt (c.chT (k + 1)) PP (c.chi (k + 1) PP)⁻¹) ∧ GlobalTheory.StepLaw.UnrOff (c.chS (k + 1)) c.Pg ∧ GlobalTheory.StepLaw.UnrOff (c.chT (k + 1)) c.Pg := by
  intro D c hc k hk
  obtain ⟨H, hEq, hres⟩ := hc.res ⟨k, hk⟩
  have hμR : ∀ PP ∈ c.Pg, ResAt (c.μ (k + 1)) PP (c.chi (k + 1) PP)⁻¹ := fun PP hP =>
    (GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D _ H hEq PP).1 _ (GlobalTheory.T.heckeChar_tameAt_of_factors_through_residue D H PP _ (hres PP hP)) (hres PP hP)
  have hμU : UnrOff (c.μ (k + 1)) c.Pg := fun v ε hε hv =>
    GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D _ H hEq v ε hε fun P hP =>
      (GlobalTheory.ChrTie.unrAt_iff_and_val_eq D _ H hEq P).1.1 (hc.unr ⟨k, hk⟩ P fun hm => by
        obtain ⟨PP, hPP, he⟩ := Finset.mem_image.1 hm
        exact hv PP hPP (he.trans hP))
  have hη : UnramEverywhere D c.η := hc.chars.2.1
  have hηR : ∀ PP, ResAt c.η⁻¹ PP 1 := fun PP => by
    have := (GlobalTheory.ExportSeries.TupleChars.resAt_of_unramEverywhere hη PP).inv
    rwa [inv_one] at this
  have hηU : UnrOff c.η⁻¹ c.Pg := UnrOff.inv fun v ε hε _ => GlobalTheory.AdTh.unr_of hη hε
  have hmR : ∀ PP ∈ c.Pg, ResAt (c.μ (k + 1) * c.η⁻¹) PP (c.chi (k + 1) PP)⁻¹ := fun PP hP => by
    have := (hμR PP hP).mul (hηR PP)
    rwa [mul_one] at this
  have hmU : UnrOff (c.μ (k + 1) * c.η⁻¹) c.Pg := hμU.mul hηU
  unfold Com.chS Com.chT Lift.chrStep
  split_ifs
  · exact ⟨fun PP hP => ⟨hmR PP hP, hμR PP hP⟩, hmU, hμU⟩
  · exact ⟨fun PP hP => ⟨hμR PP hP, hmR PP hP⟩, hμU, hmU⟩

end GlobalTheory.ChainOnto
