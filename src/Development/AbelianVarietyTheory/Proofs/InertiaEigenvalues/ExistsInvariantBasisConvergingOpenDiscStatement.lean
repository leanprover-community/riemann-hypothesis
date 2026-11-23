module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisConvergingOpenDisc
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

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.exists_invariant_basis_converging_open_disc : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ), ∀ (r m m' : ℕ) (Gm : Γ.Gam → Matrix (Fin r) (Fin r) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))) (Pm Pm' : Matrix (Fin r) (Fin r) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))), (∀ g h, Gm (g * h) = Gm g * (Gm h).map (letγ (R.γ₀ g))) → (∀ g i j k, PowerSeries.constantCoeff (Gm g i j k) = if i = j then 1 else 0) → Pm * Pm' = (R.Q ^ m') • (1 : Matrix (Fin r) (Fin r) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))) → (∀ g, (letγ (R.γ₀ g) R.Q ^ m) • (Pm * (Gm g).map (letφ R.φ₀)) = (R.Q ^ m) • (Gm g * Pm.map (letγ (R.γ₀ g)))) → ∃ (U V : Matrix (Fin r) (Fin r) (LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)))) (w : ℕ), U * V = 1 ∧ (∀ i j k, PowerSeries.constantCoeff (U i j k) = if i = j then 1 else 0) ∧ (∀ i j k, Conv (logS LL ^ w * U i j k) ∧ Conv (logS LL ^ w * V i j k)) ∧ (∀ g, (Gm g).map toLL * U.map (fun a k => PowerSeries.subst (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) (R.γ₀ g PowerSeries.X)) (a k)) = U) ∧ ∃ Cm : Matrix (Fin r) (Fin r) (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥LL.1), Pm.map toLL * U.map (fun a k => PowerSeries.subst ((1 + PowerSeries.X) ^ l - 1 : PowerSeries ↥LL.1) (a (k - 1))) = (toLL R.Q ^ m) • (U * Cm.map (fun c k => PowerSeries.C (c k))) := by
  first | exact @GlobalTheory.HWL.exists_invariant_basis_conv | exact GlobalTheory.HWL.exists_invariant_basis_conv | (intros; apply GlobalTheory.HWL.exists_invariant_basis_conv <;> assumption)
