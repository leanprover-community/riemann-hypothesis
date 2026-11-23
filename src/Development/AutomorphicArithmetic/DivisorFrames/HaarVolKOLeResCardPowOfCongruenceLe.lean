module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.OmAUnipFourierInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialFourierSumInverseOfLatticeDepth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.LocalEmbeddings.ArchSz

@[expose] public section

open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel GlobalTheory.ConjSize

open GlobalTheory.FunObj.GivenAdm in
theorem UpperTheory.haarVol_KO_le_resCard_pow_of_congruence_le :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A : Type} [Fintype A] [DecidableEq A] {J : Subgroup (GL A k)}, IsOpen (J : Set (GL A k)) → J ≤ GlobalTheory.SplitWeil.KO k A → ∀ {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) ≤ J → (haarVol J).real (GlobalTheory.SplitWeil.KO k A : Set (GL A k)) ≤ (resCard k : ℝ) ^ (e * Fintype.card A * Fintype.card A) := by
  intro k _ _ _ _ _ _ A _ _ J hJo hJK ϖ e hϖ hN
  classical
  let red : GL A k → Matrix A A (Res k e) := fun g i j =>
    if h : (g : Matrix A A k) i j ∈ 𝒪[k] then Ideal.Quotient.mk (𝓂[k] ^ e) ⟨_, h⟩ else 0
  have key : ∀ g ∈ KO k A, ∀ h ∈ KO k A, red g = red h →
      h⁻¹ * g ∈ glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) := by
    intro g hg h hh hgh
    rw [GlobalTheory.FunObj.GivenAdm.mem_glLatCong]
    refine ⟨mul_mem (inv_mem hh) hg, ?_⟩
    have hg' := (mem_KO_iff g).1 hg
    have hh' := (mem_KO_iff h).1 hh
    have e1 : ((h⁻¹ * g : GL A k) : Matrix A A k) - 1
        = ((h⁻¹ : GL A k) : Matrix A A k) * ((g : Matrix A A k) - (h : Matrix A A k)) := by
      rw [Matrix.mul_sub, Units.val_mul, ← Units.val_mul h⁻¹ h, inv_mul_cancel, Units.val_one]
    rw [e1]
    refine GlobalTheory.FunObj.GivenAdm.CongM.mul_left ?_ (fun i j => hh'.2 i j)
    intro i j
    have hij := congrFun (congrFun hgh i) j
    simp only [red, dif_pos (hg'.1 i j), dif_pos (hh'.1 i j)] at hij
    rw [Ideal.Quotient.eq] at hij
    have hv := (Model.val_le_iff_mem hϖ e _).1 hij
    simpa [Matrix.sub_apply] using hv
  haveI := isHaarMeasure_haarVol hJo hJK
  have hNJ : haarVol J (glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) : Set (GL A k)) ≤ 1 := by
    rw [← haarVol_self hJo hJK]
    exact measure_mono hN
  have piece : ∀ M : Matrix A A (Res k e), haarVol J {g | g ∈ KO k A ∧ red g = M} ≤ 1 := by
    intro M
    by_cases hne : ∃ g0, g0 ∈ KO k A ∧ red g0 = M
    · obtain ⟨g0, hg0, hM⟩ := hne
      calc haarVol J {g | g ∈ KO k A ∧ red g = M}
          ≤ haarVol J ((fun h => g0⁻¹ * h) ⁻¹'
              (glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) : Set (GL A k))) := by
            apply measure_mono
            rintro g ⟨hg, hgM⟩
            exact key g hg g0 hg0 (hgM.trans hM.symm)
        _ = haarVol J (glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) : Set (GL A k)) :=
            measure_preimage_mul _ _ _
        _ ≤ 1 := hNJ
    · calc haarVol J {g | g ∈ KO k A ∧ red g = M} ≤ haarVol J ∅ := by
            apply measure_mono
            intro g hg
            exact absurd ⟨g, hg⟩ hne
        _ = 0 := measure_empty
        _ ≤ 1 := zero_le_one
  have hKO : haarVol J (KO k A : Set (GL A k))
      ≤ (Fintype.card (Matrix A A (Res k e)) : ENNReal) := by
    calc haarVol J (KO k A : Set (GL A k))
        ≤ haarVol J (⋃ M ∈ (Finset.univ : Finset (Matrix A A (Res k e))),
            {g | g ∈ KO k A ∧ red g = M}) := by
          apply measure_mono
          intro g hg
          simp only [Set.mem_iUnion]
          exact ⟨red g, Finset.mem_univ _, hg, rfl⟩
      _ ≤ ∑ M ∈ (Finset.univ : Finset (Matrix A A (Res k e))),
            haarVol J {g | g ∈ KO k A ∧ red g = M} := measure_biUnion_finset_le _ _
      _ ≤ ∑ M ∈ (Finset.univ : Finset (Matrix A A (Res k e))), (1 : ENNReal) :=
          Finset.sum_le_sum (fun M _ => piece M)
      _ = (Fintype.card (Matrix A A (Res k e)) : ENNReal) := by
          simp [Finset.card_univ]
  have hcard : Fintype.card (Matrix A A (Res k e))
      = resCard k ^ (e * Fintype.card A * Fintype.card A) := by
    have h1 : Fintype.card (Matrix A A (Res k e))
        = Fintype.card (Res k e) ^ (Fintype.card A * Fintype.card A) := by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
      show Nat.card (A → A → Res k e) = _
      rw [Nat.card_fun, Nat.card_fun, ← pow_mul, mul_comm]
    rw [h1, GlobalTheory.FlipMatch.FourierInv.card_res_pow, ← pow_mul, mul_assoc]
  rw [measureReal_def]
  have := ENNReal.toReal_mono (by simp) hKO
  rw [hcard] at this
  simpa using this
