module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CycPow

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F) {LL : Type} [Field LL] [Algebra Qp LL]

theorem step (u : F) (hu : PD.ι PD.t * u = 1) (hu' : u ∈ PD.Fil (-1)) (n : ℤ) :
    finrank LL ↥(DdR PD (charRep (cycLL PD LL ^ (n + 1)))) =
        finrank LL ↥(DdR PD (charRep (cycLL PD LL ^ n))) ∧
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), finrank LL ↥(FildR PD (charRep (cycLL PD LL ^ (n + 1))) τ (a - 1)) =
        finrank LL ↥(FildR PD (charRep (cycLL PD LL ^ n)) τ a) := by
  have htw : IsTwistRep (cycLL PD LL) (charRep (cycLL PD LL ^ n)) (charRep (cycLL PD LL ^ (n + 1))) := by
    refine ⟨LinearEquiv.refl LL LL, fun g x => ?_⟩
    rw [zpow_add_one]
    change (((cycLL PD LL ^ n) g * cycLL PD LL g : LLˣ) : LL) * x =
      ((cycLL PD LL g : LLˣ) : LL) * ((((cycLL PD LL ^ n) g : LLˣ) : LL) * x)
    rw [Units.val_mul]
    ring
  obtain ⟨Φ, hD, hF⟩ := GlobalTheory.DRFil.exists_twist_equiv PD _ _ htw u hu hu'
  exact ⟨by rw [← hD, LinearEquiv.finrank_map_eq], fun τ a => by rw [← hF, LinearEquiv.finrank_map_eq]⟩

theorem isDR_and_finrank [CharZero Qp] [FiniteDimensional Qp LL] (u : F) (hu : PD.ι PD.t * u = 1)
    (hu' : u ∈ PD.Fil (-1)) (k : ℤ) :
    IsDR PD (charRep (cycLL PD LL ^ k)) ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      finrank LL ↥(FildR PD (charRep (cycLL PD LL ^ k)) τ a) = if a ≤ -k then 1 else 0 := by
  induction k using Int.induction_on with
  | zero =>
    have h1 : charRep (1 : G →* LLˣ) = Representation.trivial LL G LL := by
      ext g
      simp [charRep]
    rw [zpow_zero, h1, neg_zero]
    exact ⟨GlobalTheory.CrysExt.isDR_trivial PD, GlobalTheory.CrysExt.finrank_fildR_trivial PD⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := step PD (LL := LL) u hu hu' n
    refine ⟨h1.trans ih.1, fun τ a => ?_⟩
    have h3 := h2 τ (a + 1)
    rw [add_sub_cancel_right] at h3
    rw [h3, ih.2]
    exact if_congr (by omega) rfl rfl
  | pred n ih =>
    obtain ⟨h1, h2⟩ := step PD (LL := LL) u hu hu' (-(n : ℤ) - 1)
    rw [sub_add_cancel] at h1 h2
    refine ⟨h1.symm.trans ih.1, fun τ a => ?_⟩
    rw [← h2, ih.2]
    exact if_congr (by omega) rfl rfl

end Generic

theorem cyc_zpow_crys_dR_jump : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (k : ℤ), IsCrys (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) ∧ IsDR (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) τ a = if a = -k then 1 else 0 := by
  intro l _ P AI T K LL k
  have := LL.2
  obtain ⟨u, hu', hu⟩ := ((GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI T).2.2 K (-1) 1).1
    (by rw [neg_add_cancel]; exact (P.PD K).one_mem)
  have ht : (P.PD K).ι (P.PD K).t * u = 1 := by
    rw [P.PD_ι, P.period_datum_t_eq]
    exact hu.symm
  obtain ⟨h1, h2⟩ := isDR_and_finrank (P.PD K) (LL := ↥LL.1) u ht hu' k
  refine ⟨GlobalTheory.BlockCrys.isCrys_cyc_zpow _ k, h1, fun τ a => ?_⟩
  rw [multV, h2, h2]
  split_ifs <;> first | rfl | omega

end GlobalTheory.CycPow
