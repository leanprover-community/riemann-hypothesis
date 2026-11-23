module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGammaLayerPadicCoordinates
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

theorem _root_.GlobalTheory.T.exists_gammaLayer_padic_coordinates : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ Γ : GamS P K s LL, (∃ lam : ↥Γ.GKs →* Multiplicative ℤ_[l], Continuous lam ∧ (∀ g, lam g = 1 ↔ Γ.resΓ (g : ↥(GK K)) = 1) ∧ (∀ g, lam g = Multiplicative.ofAdd 1 ↔ Γ.resΓ (g : ↥(GK K)) = Γ.gam) ∧ (∃ g, lam g = Multiplicative.ofAdd 1) ∧ IsClosed (Γ.GKs : Set ↥(GK K))) ∧ ∃ lam : ↥(GK K) →* Multiplicative ℤ_[l], Continuous lam ∧ (∀ g, lam g = 1 ↔ Γ.resΓ g ∈ Γ.DelF) ∧ (∀ g, Γ.resΓ g = Γ.gamK → lam g = Multiplicative.ofAdd 1) := by
  first | exact @GlobalTheory.HWL.Coord.exists_gamma_coordinates | exact GlobalTheory.HWL.Coord.exists_gamma_coordinates | (intros; apply GlobalTheory.HWL.Coord.exists_gamma_coordinates <;> assumption)
