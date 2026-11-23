module

public import Formalism.HermitianCurvature.StatementTBB
public import Formalism.HermitianCurvature.HerGenC
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HsInnerSelfEqNormSq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqIntegralInnerTopVectorsStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

theorem levelZero_cut_eq_integral_Ew : P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε : ℝ, 0 < ε → (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re = ∫ c : Fin (P.r + 1) → ℂ, TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c) := by
  intro hA Cb
  obtain ⟨Cc, hCc⟩ := GlobalTheory.T.levelZeroPairing_eq_integral_inner_topVectors hA Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ A N w hD hχ hf hdec hAle hw hN ε hε
  have h := hCc Wp Wq P p f χ A N w hD hχ hf hdec hAle hw hN ε ε hε hε
  have hF := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hf ε
  have h0 : p.RR (D.cutF p.T.base χ f ε) 0 w [] [] =
      ∫ c, inner ℂ (tv p (D.cutF p.T.base χ f ε) w c) (tv p (D.cutF p.T.base χ f ε) w c) := by
    unfold KB.Pl.RR
    rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hF (Formalism.FourierDecayAlt.P.CutBP.good_positioned_of_cut hw)]
    exact h
  have h1 : ∀ c, inner ℂ (tv p (D.cutF p.T.base χ f ε) w c) (tv p (D.cutF p.T.base χ f ε) w c) =
      ((‖tv p (D.cutF p.T.base χ f ε) w c‖ ^ 2 : ℝ) : ℂ) := fun c => by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [h0]
  simp only [h1, Ew_eq_norm_tv_sq]
  rw [integral_complex_ofReal, Complex.ofReal_re]

end GlobalTheory.TopVec
