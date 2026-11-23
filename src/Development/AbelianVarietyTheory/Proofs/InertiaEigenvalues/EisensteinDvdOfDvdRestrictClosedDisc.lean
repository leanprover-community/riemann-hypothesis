module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPolyEqZeroOfDiscDvdStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassDivisionClosedDiscBreuilKisinStatement
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem dvd_of_dvd_restrict_discS : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ∀ R : bk.DS ρ →+* bk.DS bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) R → ∀ y, toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ R y → toDisc l (X : bk.S) ρ bk.E ∣ y := by
  intro l _ K bk ρ h0 h1 R hR y hy
  obtain ⟨q, k, r, hr, e⟩ := GlobalTheory.T.weierstrass_division_closedDisc_breuilKisin l K bk ρ h0 h1 y
  have e' := congrArg R e
  rw [map_mul, map_add (f := _), map_mul, hR.ext, hR.ext, RingHom.id_apply, RingHom.id_apply] at e'
  have hd : toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ (r : bk.S) := by
    have h2 := hy.mul_left (R (((l : ℕ) : bk.DS ρ) ^ k))
    rw [e'] at h2
    exact (dvd_add_right (dvd_mul_right _ _)).1 h2
  have hr0 := GlobalTheory.T.breuilKisin_poly_eq_zero_of_disc_dvd l K bk r hr hd
  rw [hr0, Polynomial.coe_zero, map_zero, add_zero] at e
  exact ((isUnit_l_disc l (X : bk.S) ρ).pow k).dvd_mul_left.1 ⟨q, e⟩

end GlobalTheory.BSP
