module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuou
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyRealSelfAnnihilatorAdeleCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section
namespace GlobalTheory.SplitSvN
open MeasureTheory Matrix ComplexConjugate

variable {F : Type} [Field F] [NumberField F]

theorem schA_facts (hF : IsTotallyReal F) {κ : Type} [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ ∧ (∃ C, ∀ x, ‖Φ x‖ ≤ C) ∧
      ∀ μ : Measure (κ → AF F), μ.IsAddHaarMeasure → Integrable Φ μ := by
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  let j : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let r : (κ → AF F) ≃ₜ+ (Fin (Fintype.card κ) → AF F) :=
    { toFun := fun x => x ∘ j
      invFun := fun y => y ∘ j.symm
      left_inv := fun x => funext fun i => by simp
      right_inv := fun y => funext fun i => by simp
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_pi fun i => continuous_apply _
      continuous_invFun := continuous_pi fun i => continuous_apply _ }
  have hd := GlobalTheory.SchwartzDecay.decay_of_mem_schA F _ _ (GlobalTheory.RestrSchA.mem_schA_comp_extend F j j.injective Φ hΦ)
  set Φ' := fun y : Fin (Fintype.card κ) → AF F => Φ (Function.extend j y 0) with hΦ'
  have e : Φ = Φ' ∘ r := funext fun x => by
    show Φ x = Φ (Function.extend j (x ∘ j) 0)
    congr 1
    funext i
    obtain ⟨k, rfl⟩ := j.surjective i
    rw [j.injective.extend_apply]
    rfl
  refine ⟨e ▸ hd.1.comp r.continuous, ?_, fun μ hμ => ?_⟩
  · obtain ⟨C, hC⟩ := hd.2.2 0
    exact ⟨C, fun x => by rw [e]; simpa using hC (r x)⟩
  · have hi := (GlobalTheory.decay_integrable_periodise F _ hF Φ' hd).1 (μ.map r) (r.isAddHaarMeasure_map μ)
    rw [e]
    exact hi.comp_measurable r.continuous.measurable

def infOne : AF F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

def idem (S : Finset (Pl (F := F))) : AF F :=
  infOne + ∑ w ∈ S, GlobalTheory.LatVac.liftV w 1

end GlobalTheory.SplitSvN

end
