module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

theorem _root_.GlobalTheory.T.directSum_deRham_crystalline_jumps_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (e : V ≃ₗ[↥LL.1] (V₁ × V₂)), (∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2)) → (IsDR (P.PD K) ρ ↔ IsDR (P.PD K) ρ₁ ∧ IsDR (P.PD K) ρ₂) ∧ (IsCrys (P.PD K) ρ ↔ IsCrys (P.PD K) ρ₁ ∧ IsCrys (P.PD K) ρ₂) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) ρ τ a = multV (P.PD K) ρ₁ τ a + multV (P.PD K) ρ₂ τ a := by
  first | exact @GlobalTheory.Per.DirectSumHT.directSum_hodgeTate | exact GlobalTheory.Per.DirectSumHT.directSum_hodgeTate | (intros; apply GlobalTheory.Per.DirectSumHT.directSum_hodgeTate <;> assumption)
