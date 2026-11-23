module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdFrobXiSub
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.DualLattices.AinfFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.WinLift

theorem isUnit_of_isUnit_theta {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C]
    [CharZero C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O)
    (z : Ainf p O) (hz : IsUnit (WittVector.fontaineTheta O p z)) : IsUnit z := by
  haveI := GlobalTheory.AinfXi.isLocalRing_ainf (p := p) hv
  haveI := ReciprocityTheory.PGsh.Ainf.O_local O hv
  by_contra hn
  obtain ⟨w, hw⟩ := ReciprocityTheory.PGsh.Ainf.theta_surj p O hv (↑hz.unit⁻¹ : O)
  have hm : z ∈ IsLocalRing.maximalIdeal (Ainf p O) := (IsLocalRing.mem_maximalIdeal _).2 hn
  have hk : z * w - 1 ∈ IsLocalRing.maximalIdeal (Ainf p O) := by
    apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (WittVector.fontaineTheta O p))
    rw [RingHom.mem_ker, map_sub, map_mul, hw, map_one, IsUnit.mul_val_inv, sub_self]
  have h1 := Ideal.sub_mem _ (Ideal.mul_mem_right w _ hm) hk
  rw [sub_sub_cancel] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal (Ainf p O)).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem exists_unit_lift_mod_tau : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (U : Matrix ι ι F.B), IsUnit U → ∃ V : Matrix ι ι (Ainf p O), IsUnit V ∧ ∀ i j, F.τ ∣ U i j - F.a (V i j) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F ι _ _ U hU
  choose x y hxy using fun i j => F.gen (U i j)
  refine ⟨Matrix.of x, ?_, fun i j => ⟨F.a (y i j), by rw [hxy i j]; simp⟩⟩
  have hτ := GlobalTheory.WinLift.theta_tau F hv hε
  have e : F.θ.mapMatrix (F.a.mapMatrix (Matrix.of x)) = F.θ.mapMatrix U :=
    Matrix.ext fun i j => by simp [hxy i j, hτ]
  have hdet : WittVector.fontaineTheta O p (Matrix.of x).det = F.θ U.det := by
    rw [← F.θ_a, RingHom.map_det, RingHom.map_det, e, ← RingHom.map_det]
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_of_isUnit_theta hv
  rw [hdet]
  exact ((Matrix.isUnit_iff_isUnit_det U).1 hU).map F.θ

end GlobalTheory.WinLift
