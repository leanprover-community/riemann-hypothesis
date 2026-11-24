module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem dvd_σF_self {l : ℕ} [Fact l.Prime] (g : GQ l) (x : Per.Fl l) : x ∣ Per.σF g x := by
  apply GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd
  rw [GlobalTheory.RingBasics.untilt_σF]
  generalize x.untilt = y
  by_cases hy : (y : ℂ_[l]) = 0
  · obtain rfl : y = 0 := Subtype.ext hy
    simp
  · refine ⟨⟨Per.σC g y / y, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div, GlobalTheory.RingBasics.norm_σC, div_self (norm_ne_zero_iff.2 hy)]
    · rw [GlobalTheory.RingIface.sigO_coe]
      change Per.σC g y = (y : ℂ_[l]) * (Per.σC g y / y)
      field_simp

theorem galois_discMap : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    (∀ g : GQ l, bk.ev X ∣ Per.σA g (bk.ev X)) ∧ ∀ (ρ : ℝ≥0), 0 < ρ → ∀ g : GQ l,
      ∃ G : bk.DA ρ →+* bk.DA ρ, IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G := by
  intro l _ K bk
  have h : ∀ g : GQ l, bk.ev X ∣ Per.σA g (bk.ev X) := fun g => by
    rw [bk.ev_X, GlobalTheory.RingIface.sigA_teich]
    exact map_dvd (WittVector.teichmuller l) (dvd_σF_self g bk.flat)
  refine ⟨h, fun ρ hρ g => ⟨_, isDiscMap_map (Per.σA g) ?_⟩⟩
  obtain ⟨c, hc⟩ := h g
  have h1 := norm_toDisc_pow_le (l := l) (u := bk.ev X) 1 hρ
  rw [pow_one, pow_one] at h1
  rw [hc, map_mul]
  exact (norm_mul_le _ _).trans ((mul_le_mul h1 (norm_toDisc_le c) (norm_nonneg _) ρ.2).trans (mul_one _).le)

end GlobalTheory.BSP
