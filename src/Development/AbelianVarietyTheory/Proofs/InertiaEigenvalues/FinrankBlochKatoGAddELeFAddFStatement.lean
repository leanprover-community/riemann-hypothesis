module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrystallineCocycles
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankBlochKatoGAddELeFAddF
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

theorem _root_.GlobalTheory.T.finrank_blochKato_g_add_e_le_f_add_f : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v, Continuous fun g => ρ g v) → (∀ y, Continuous fun g => ρ' g y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' → IsDual1 (P.PD K) ρ ρ' m → finrank ℚ_[l] ↥(geometricCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ') ≤ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ') := by
  first | exact @GlobalTheory.HyodoDef.Count.finrank_blochKato_g_add_e_le_f_add_f_alt | exact GlobalTheory.HyodoDef.Count.finrank_blochKato_g_add_e_le_f_add_f_alt | (intros; apply GlobalTheory.HyodoDef.Count.finrank_blochKato_g_add_e_le_f_add_f_alt <;> assumption)
