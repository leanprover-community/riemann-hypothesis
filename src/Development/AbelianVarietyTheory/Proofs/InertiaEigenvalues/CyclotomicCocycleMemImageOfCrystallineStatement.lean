module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCocycleMemImageOfCrystalline
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

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

theorem _root_.GlobalTheory.T.cyclotomicCocycle_mem_image_of_crystalline : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∀ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (lam : ↥((HW l).W K s LL h).GKs →* Multiplicative ℤ_[l]), Continuous lam → (∀ g, lam g = 1 → ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1) → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → ∀ g₁ : ↥((HW l).W K s LL h).GKs, lam g₁ = Multiplicative.ofAdd 1 → ∀ z₁ ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₁ = ((F l).E K s LL h).tie.jD T z₁ → ∀ g : ↥((HW l).W K s LL h).GKs, ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = ((F l).E K s LL h).tie.jD T z := by
  first | exact @GlobalTheory.NL.ZVal.zval | exact GlobalTheory.NL.ZVal.zval | (intros; apply GlobalTheory.NL.ZVal.zval <;> assumption)
