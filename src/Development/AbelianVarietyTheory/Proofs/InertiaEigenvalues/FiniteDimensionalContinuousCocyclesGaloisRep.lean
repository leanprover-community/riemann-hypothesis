module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTop
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoExactAnnihilatorsPeriodDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateTwistDualPerfectPairingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1DualPairStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import GroundTheory.LocalFields.Examples
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrystallineCocycles

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

namespace GlobalTheory.HyodoFin

theorem finite_continuous_cocycles_localGaloisRep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V]
    [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
    [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V),
    (∀ v, Continuous fun g => ρ g v) → Module.Finite ℚ_[l] ↥(continuousCocycles ρ) := by
  intro l _ P K V _ _ _ _ _ _ _ ρ hc
  obtain ⟨ρ', m, hc', hD⟩ := GlobalTheory.T.exists_tateTwistDual_perfectPairing l P K V ρ hc
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let A : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V, ρ := ρ, cont := hc }
  let A' : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] :=
    { V := Fin (finrank ℚ_[l] V) → ℚ_[l], ρ := ρ', cont := hc' }
  have hH := (GlobalTheory.T.finrank_H1_dual_pair CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler l P K ℚ_[l] ℤ_[l]
    GlobalTheory.Published.BlochKato.goodO_padicInt A A' m hD).1
  exact GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A hH

end GlobalTheory.HyodoFin
