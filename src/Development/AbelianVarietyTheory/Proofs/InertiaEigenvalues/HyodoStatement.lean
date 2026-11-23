module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFiltrationDualityStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateTwistDualPerfectPairingStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalContinuousCocyclesGaloisRepStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankBlochKatoGAddELeFAddFStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankFiniteLeExponentialCocyclesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsSemistableStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableCocyclesBetweenBlochKatoAndContinuousStatement
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import GroundTheory.LocalFields.Examples
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrystallineCocycles

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.HyodoDef TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem hyodo : Hyodo := by
  intro l _ P AI T K V _ _ _ _ _ ρ hcont hsst c hc hcoc hdR
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  haveI : ContinuousSMul ℚ_[l] V := IsModuleTopology.toContinuousSMul ℚ_[l] V
  obtain ⟨ρ', m, hρ'c, hdual⟩ := GlobalTheory.T.exists_tateTwistDual_perfectPairing l P K V ρ hcont
  have hdrV : IsDR (P.PD K) ρ := GlobalTheory.T.isDeRham_of_isSemistable l P AI T K V ρ hsst
  have hdrV' : IsDR (P.PD K) ρ' := by
    letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
    haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    exact (GlobalTheory.T.de_rham_filtration_duality l P AI T K).1 ℚ_[l] ℤ_[l] GlobalTheory.Published.BlochKato.goodO_padicInt
      { V := V, ρ := ρ, cont := hcont } { V := Fin (finrank ℚ_[l] V) → ℚ_[l], ρ := ρ', cont := hρ'c } m hdrV hdual
  have hfin : Module.Finite ℚ_[l] ↥(continuousCocycles ρ) := GlobalTheory.T.finiteDimensional_continuousCocycles_galoisRep l P K V ρ hcont
  obtain ⟨S, _hfS, hSc, hSst, hSdR, hS⟩ := GlobalTheory.T.semistable_cocycles_between_blochKato_and_continuous l P AI T K V _ ρ ρ' m hcont hdual hsst hfin
  have hgc : geometricCocycles (P.PD K) ρ ≤ continuousCocycles ρ := fun _ h => h.1
  haveI : Module.Finite ℚ_[l] ↥(geometricCocycles (P.PD K) ρ) :=
    Module.Finite.of_injective (Submodule.inclusion hgc) (Submodule.inclusion_injective hgc)
  have hSg : S ≤ geometricCocycles (P.PD K) ρ := fun c hc => ⟨hSc hc, hSdR c hc⟩
  have h1 := GlobalTheory.T.finrank_blochKato_g_add_e_le_f_add_f l P AI T K V ρ _ ρ' m hcont hρ'c hdrV hdrV' hdual
  have h2 := GlobalTheory.T.finrank_finite_le_exponential_cocycles l P AI T K _ ρ' hρ'c hdrV'
  have hEq : S = geometricCocycles (P.PD K) ρ := Submodule.eq_of_le_of_finrank_le hSg (by omega)
  have hcg : c ∈ geometricCocycles (P.PD K) ρ := ⟨⟨hc, hcoc⟩, hdR⟩
  rw [← hEq] at hcg
  exact hSst c hcg

end GlobalTheory.PMon
