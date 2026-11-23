module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpOneAtEmbedding
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

theorem _root_.GlobalTheory.T.crystalline_character_jump_one_at_embedding : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  first | exact @GlobalTheory.HWL.charRep_crys_jump_one | exact GlobalTheory.HWL.charRep_crys_jump_one | (intros; apply GlobalTheory.HWL.charRep_crys_jump_one <;> assumption)
