module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolMulPosLeConj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerCommensurableInvVolumeSmulComplement
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordDatum

theorem exists_invVol_eq_mul {G : Type} [Group G] (K' K0 : Subgroup G) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ K : Subgroup G, K0.relIndex K ≠ 0 → K.relIndex K0 ≠ 0 →
      invVol K' K = κ * invVol K0 K := by
  by_cases hc : K'.relIndex K0 ≠ 0 ∧ K0.relIndex K' ≠ 0
  · refine ⟨invVol K' K0, ?_, fun K hK hK' => ?_⟩
    · unfold invVol
      positivity
    · exact (invVol_mul_pos_le_conj K' K0 K hc.1 hc.2
        (Subgroup.relIndex_ne_zero_trans hc.1 hK)
        (Subgroup.relIndex_ne_zero_trans hK' hc.2)).1
  · refine ⟨0, le_rfl, fun K hK hK' => ?_⟩
    rw [zero_mul]
    unfold invVol
    by_cases h1 : K.relIndex K' = 0
    · simp [h1]
    · have h2 : K'.relIndex K = 0 := by
        by_contra h2
        exact hc ⟨Subgroup.relIndex_ne_zero_trans h2 hK', Subgroup.relIndex_ne_zero_trans hK h1⟩
      simp [h2]

theorem exists_wt_eq_mul_nu : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ d0 : LocNG.Datum P, ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (d : LocNG.Datum P) Λ, S.IsTerm (c.dat d) Λ → LocNG.Datum.wt d0 d = κ * S.nu (c.dat d) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c d0
  have := hM.loc
  have := hM.char0
  obtain ⟨κ, hκ, hK⟩ :=
    exists_invVol_eq_mul (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d0)) S.complementReferenceCompactSubgroup
  refine ⟨κ, hκ, fun d Λ hT => ?_⟩
  obtain ⟨h1, h2⟩ := (Frames.stab_commensurable_invVol_smul M.L r k S).2 (c.dat d) Λ hT
  rw [(transport M hM H r k P S c).2.2.2.2 d0 d]
  exact hK _ h1 h2

end GlobalTheory.HL.CoordDatum
