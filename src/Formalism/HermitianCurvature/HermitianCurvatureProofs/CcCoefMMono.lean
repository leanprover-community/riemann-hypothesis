module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormLevLimit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactlySupportedBanachModel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryU1Plain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeBoundInBanachSpace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WirtingerIntegrationByParts
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Countable
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Separation.CompletelyRegular
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplySub
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceAppend

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousUnipotentVectorScalar, Formalism.HermitianCurvature.HermitianCurvatureProofs.CcCoefMMono

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousUnipotentVectorScalar =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousUnipotentVectorScalar", "h": "module\n\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactlySupportedBanachModel\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryU1Plain\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeBoundInBanachSpace\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.WirtingerIntegrationByParts\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.CategoryTheory.Countable\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Separation.CompletelyRegular\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear\n\n"}
section -- clump:auto
@[expose] public section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.LastBlockContinuity

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.JCTx6 Formalism.FourierDecayAlt.P.JCTx6.Pos Formalism.FourierDecayAlt.P.PBE

theorem continuous_unipotent_vector_scalar (n : ℕ) (v : G.UT (n + 1) → ℂ) : Continuous (fun t : ℂ => Zv n t v) := by
  show Continuous (fun t : ℂ => fun i j => (G.ptLong (n + 1) t * G.upper v) i j)
  have h : Continuous (fun t : ℂ => (G.ptLong (n + 1) t * G.upper v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) := by
    unfold G.ptLong
    exact (continuous_id.smul continuous_const).matrix_mul continuous_const
  exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp h)



theorem posCoreCont : ∃ Cc : ℝ, 0 ≤ Cc ∧
  ∀ (k ph n ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (z z' : Fin (2 * (ph + (n + 1) + ρ) + k + 1) → ℂ), inWb k (ph + (n + 1) + ρ) z → inWb k (ph + (n + 1) + ρ) z' →
    ∀ (Θ : B.DiffOp k (ph + (n + 1) + ρ) Wp Wq) (o κ : ℕ), U.InDD k (ph + (n + 1)) ρ o κ Θ →
    ∀ (χ : ℝ → ℝ) (A₀ ε : ℝ), C6.IsCut0 χ → 0 < ε →
    ∀ (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t0 : ℂ), (∀ i, d i ≠ 0) → t0 ≠ 0 →
    ∀ (As mm : ℕ) (A : ℝ), o ≤ As → κ + (ph + (n + 1)) * o ≤ As → mm ≤ As →
      (2 * (ph + (n + 1) + ρ) + k + 1) ^ 3 ≤ As →
      A ≤ 128 * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 3 * (As : ℝ) →
      Cc * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A₀ →
      ∃ ε' : ℝ, 0 < ε' ∧
      ∀ (f : B.Mat k (ph + (n + 1) + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ (3 * As) f c →
      ∀ F : B.Mat k (ph + (n + 1) + ρ) → (Wq →L[ℂ] Wp),
        (∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
          F g = B.opApply Θ (fun x => ((χ (Gf k (ph + (n + 1) + ρ) z z' x / ε) : ℝ) : ℂ) • f x) g) →
        ∃ (δ Kb : ℝ) (Dd : ℂ → ℝ), 0 < δ ∧ Tendsto Dd (𝓝 t0) (𝓝 0) ∧ ∀ t : ℂ, dist t t0 < δ → t ≠ 0 ∧
          B.CCle A mm (fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ) Kb ∧
          (∀ γ ∈ B.GV k ρ, U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ ≠ 0 →
            ε' ≤ Gf k ρ (U.lowV k (ph + (n + 1)) ρ z) (U.lowV k (ph + (n + 1)) ρ z') γ) ∧
          B.CCle A mm (fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ - U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t0) z z' F (fun a => a.elim0) γ) (Dd t) := by
  obtain ⟨Cc, hCc, hNear⟩ := posCoreNear_of Formalism.FourierDecayAlt.P.JCTx6.Int.intG
    Formalism.FourierDecayAlt.P.JCTx6.Int.orbit_slice_integrable
  refine ⟨Cc, hCc, ?_⟩
  intro k ph n ρ Wp Wq _ _ _ _ _ _ z z' hz hz' Θ o κ hΘ χ A₀ ε hχ hε σ d t0 hd ht0 As mm A ho hκ
    hmm hAs hA hA₀
  obtain ⟨ε', K, hε', _, hpack⟩ := hNear k ph n ρ Wp Wq z z' hz hz' Θ o κ hΘ χ A₀ ε hχ hε σ d t0 hd
    ht0 As mm A ho hκ hmm hAs hA hA₀
  refine ⟨ε', hε', ?_⟩
  intro f c hc F hF
  obtain ⟨δ, Dd, hδ, hDd, htnear⟩ := hpack f c hc F hF
  refine ⟨δ, K * c, Dd, hδ, hDd, fun t ht => ?_⟩
  obtain ⟨htne, hCC, hsupp, hdiff, _⟩ := htnear t ht
  exact ⟨htne, hCC, hsupp, hdiff⟩

end Formalism.FourierDecayAlt.P.LastBlockContinuity
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousUnipotentVectorScalar =====

-- ===== clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CcCoefMMono =====
-- clump-header: {"m": "Formalism.HermitianCurvature.HermitianCurvatureProofs.CcCoefMMono", "h": "module\n\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormLevLimit\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting\npublic import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousUnipotentVectorScalar\nimport Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplySub\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.LastBlockContinuity

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem xs_eq_phi {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (ε : ℝ) (i : ℕ) (hi : i ≤ r) (w : List C.Letter)
    (a : Wd.Ix (Fin w.length)) (h0 : C.LPt) (n : ℕ) (t : ℂ) (hc : r - i = r - D.ptSize (h0 ++ [(n + 1, t)]))
    (hpb : ∀ b ∈ h0, 1 ≤ b.1 ∧ b.2 ≠ 0) (ht : t ≠ 0) (hsz : D.ptSize (h0 ++ [(n + 1, t)]) = i)
    (e1 : r = D.ptSize h0 + (n + 1) + (r - i)) (e2 : D.ptSize h0 + (n + 1) + (r - i) = r)
    (hh : B.Mat k r → (Wq →L[ℂ] Wp)) :
    PBE.xs T χ ε i hi w (h0 ++ [(n + 1, t)]) hc hh a =
      fun γ => U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ := by
  subst hsz
  have hloc : D.IsLocPt (h0 ++ [(n + 1, t)]) (D.ptSize (h0 ++ [(n + 1, t)])) := by
    refine ⟨fun b hb => ?_, rfl⟩
    rcases List.mem_append.mp hb with hb | hb
    · exact hpb b hb
    · simp only [List.mem_singleton] at hb
      subst hb
      exact ⟨by omega, ht⟩
  unfold PBE.xs
  rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_self]
  funext γ
  exact Formalism.FourierDecayAlt.P.SliceAppend.slice_append k r T.base.z T.base.z'
    (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h0 ++ [(n + 1, t)])) hi w a)
    h0 n t hloc hi γ

theorem ccCoefM_mono {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {Bs : B.RealPlaceData k r Wp Wq} {A : ℝ} {mm : ℕ} {e e' : ℝ} {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h : JC.CCCoefM Bs A mm e F) (he : e' ≤ e) : JC.CCCoefM Bs A mm e' F :=
  ⟨h.1, h.2.1, fun g hg hne => le_trans he (h.2.2 g hg hne)⟩

theorem sliceContQa : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ Cc : ℝ, Cs ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r) (w : List C.Letter), w.length ≤ N →
    ∀ (h0 : C.LPt) (m : ℕ) (hc : ∀ t : ℂ, r - i = r - D.ptSize (h0 ++ [(m, t)])),
    (∀ b ∈ h0, 1 ≤ b.1 ∧ b.2 ≠ 0) → 1 ≤ m → D.ptSize h0 + m = i →
    ∀ t0 : ℂ, t0 ≠ 0 → ∀ (a : Wd.Ix (Fin w.length)), ∃ ε' : ℝ, 0 < ε' ∧
      ∀ (h : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV k r) h →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h c →
        ∃ (δ Kb : ℝ) (Dd : ℂ → ℝ), 0 < δ ∧ Tendsto Dd (𝓝 t0) (𝓝 0) ∧ ∀ t : ℂ, dist t t0 < δ → t ≠ 0 ∧
          JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε' (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a) ∧
          B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a) Kb ∧
          JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε'
            (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a - PBE.xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc t0) h a) ∧
          B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N)
            (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a - PBE.xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc t0) h a) (Dd t) := by
  obtain ⟨Cp, hCp0, hCp⟩ := posCoreCont
  refine ⟨16 * Cp, by positivity, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi w hw h0 m hc hpb hm hsz t0 ht0 a
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hPt : ∀ t : ℂ, D.ptSize (h0 ++ [(n + 1, t)]) = i := fun t => by
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append]; exact hsz
  have hd0 : ∀ q, D.ptDiag h0 q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h0 hpb q q.2
  have e1 : r = D.ptSize h0 + (n + 1) + (r - i) := by omega
  have e2 : D.ptSize h0 + (n + 1) + (r - i) = r := by omega
  have hj1 : 1 ≤ D.ptSize h0 + (n + 1) := by omega
  obtain ⟨Θ, hΘ, hΘF⟩ := Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD k (D.ptSize h0 + (n + 1)) (r - i) Wp Wq (D.castV e1 T.base.z)
    (D.castV e1 T.base.z') (by omega) w a hj1
  have hU : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh →
      ∀ g ∈ B.GV k (D.ptSize h0 + (n + 1) + (r - i)), U.DjU k (D.ptSize h0 + (n + 1)) (r - i) g ≠ 0 →
      D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a) g =
        B.opApply Θ (D.castF e2 (D.cutF T.base χ hh ε)) g := by
    intro hh hsm g hg hD
    have hFc : B.CkOn ⊤ (B.GV k r) (D.cutF T.base χ hh ε) := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hsm ε
    have h1 : D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a) =
        D.uwG k (D.ptSize h0 + (n + 1) + (r - i)) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
          (D.castF e2 (D.cutF T.base χ hh ε)) (D.ptSize h0 + (n + 1)) (by omega) w a := by
      rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]
      exact Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ hsz.symm _ _ w a
    rw [h1, hΘF _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFc) g hg hD]
  have hFrel : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh →
      ∀ g ∈ B.GV k (D.ptSize h0 + (n + 1) + (r - i)), U.DjU k (D.ptSize h0 + (n + 1)) (r - i) g ≠ 0 →
      D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a) g =
        B.opApply Θ (fun x => ((χ (Gf k (D.ptSize h0 + (n + 1) + (r - i)) (D.castV e1 T.base.z)
          (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) • D.castF e2 hh x) g := by
    intro hh hsm g hg hD
    rw [hU hh hsm g hg hD, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_cutF e2]
  set nd := 2 * r + k + 1 with hnd
  set As := 11 * (N * nd ^ 2 + nd ^ 3) + 5 with hAs
  obtain ⟨b1, b2, b3, b4, b5⟩ := Formalism.FourierDecayAlt.P.JCTx6.Link2.budgetAs r k N w.length (D.ptSize h0 + (n + 1)) hk2 hw (by omega)
  have hmmU : P5.mmUser P0 N = 5 + 3 * (r + 1) * (N + 2) * nd + N * r := by
    simp only [P5.mmUser, P5.nV, hPk, hPr, hnd]
  have hAU : P5.Auser P0 N = 127 * ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by
    simp only [P5.Auser, P5.nV, hPk, hPr, hnd]
  have hX1 : (1 : ℝ) ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3 := by exact_mod_cast b5
  have hAsR : (As : ℝ) = 11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5 := by
    rw [hAs]; push_cast; ring
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith
  have hsumR : (((D.ptSize h0 + (n + 1) + (r - i) : ℕ) : ℝ)) = (r : ℝ) := by exact_mod_cast e2
  obtain ⟨ε', hε', hQ⟩ := hCp k (D.ptSize h0) n (r - i) Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z')
    (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem)
    Θ _ _ hΘ χ A₀ ε hχ hε (D.ptPerm h0) (D.ptDiag h0) t0 hd0 ht0 As (P5.mmUser P0 N) (P5.Auser P0 N + 1)
    b1 b2 (by rw [hmmU]; exact b3) (by rw [e2]; exact b4)
    (by
      rw [hsumR, hAU, hAsR]
      have hR3 : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
      have : 0 ≤ ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by positivity
      nlinarith)
    (by
      rw [hsumR, hAsR]
      have s1 : Cp * ((r : ℝ) + 1) ^ 4 * (11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5) ≤
          Cp * ((r : ℝ) + 1) ^ 4 * (16 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      have s2 : 16 * Cp * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) ≤
          Cc * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_right hCc (by positivity)
      have s3 : Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) ≤ A₀ := by
        have hndR : (nd : ℝ) = 2 * (r : ℝ) + k + 1 := by rw [hnd]; push_cast; ring
        rw [hndR]; exact hA₀
      nlinarith)
  have hz1 : U.lowV k (D.ptSize h0 + (n + 1)) (r - i) (D.castV e1 T.base.z) = (T.bs i).z := by
    have hzl : T.base.z = D.castV (by omega) (liftVec k i (r - i) (T.bs i).z) := (T.z_lev _ hi).symm
    rw [hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hsz _ _
  have hz1' : U.lowV k (D.ptSize h0 + (n + 1)) (r - i) (D.castV e1 T.base.z') = (T.bs i).z' := by
    have hzl' : T.base.z' = D.castV (by omega) (liftVec k i (r - i) (T.bs i).z') := (T.z'_lev _ hi).symm
    rw [hzl', Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hsz _ _
  refine ⟨ε', hε', fun hh c hsm hcl => ?_⟩
  obtain ⟨δ, Kb, Dd, hδ, hDd, hnear⟩ := hQ (D.castF e2 hh) c (PBE.ccle_castF e2 hcl) _ (hFrel hh hsm)
  have key : ∀ t : ℂ, t ≠ 0 → PBE.xs T χ ε i hi w (h0 ++ [(n + 1, t)]) (hc t) hh a =
      fun γ => U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ :=
    fun t ht => xs_eq_phi T χ ε i hi w a h0 n t (hc t) hpb ht (hPt t) e1 e2 hh
  obtain ⟨-, -, hsupp0, -⟩ := hnear t0 (by rw [dist_self]; exact hδ)
  refine ⟨δ, Kb, Dd, hδ, hDd, fun t ht => ?_⟩
  obtain ⟨htne, hB, hsupp, hD⟩ := hnear t ht
  have hsub : PBE.xs T χ ε i hi w (h0 ++ [(n + 1, t)]) (hc t) hh a -
      PBE.xs T χ ε i hi w (h0 ++ [(n + 1, t0)]) (hc t0) hh a =
      fun γ => U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ -
        U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t0) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ := by
    rw [key t htne, key t0 ht0]; rfl
  rw [hsub, key t htne]
  refine ⟨htne, ⟨hB.1, ⟨_, hB⟩, fun γ hγ hne => ?_⟩, hB, ⟨hD.1, ⟨_, hD⟩, fun γ hγ hne => ?_⟩, hD⟩
  · have := hsupp γ hγ hne
    rwa [hz1, hz1'] at this
  · by_cases h1 : U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ = 0
    · have hne0 : U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
          (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t0) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
          (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ ≠ 0 := by
        intro h2; apply hne; simp only [h1, h2, sub_zero]
      have := hsupp0 γ hγ hne0
      rwa [hz1, hz1'] at this
    · have := hsupp γ hγ h1
      rwa [hz1, hz1'] at this

theorem sliceContQ : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ Cc : ℝ, Cs ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r) (w : List C.Letter), w.length ≤ N →
    ∀ (h0 : C.LPt) (m : ℕ) (hc : ∀ t : ℂ, r - i = r - D.ptSize (h0 ++ [(m, t)])),
    (∀ b ∈ h0, 1 ≤ b.1 ∧ b.2 ≠ 0) → 1 ≤ m → D.ptSize h0 + m = i →
    ∀ t0 : ℂ, t0 ≠ 0 → ∃ ε' : ℝ, 0 < ε' ∧ ∀ (a : Wd.Ix (Fin w.length))
      (h : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV k r) h →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h c →
        ∃ (δ Kb : ℝ) (Dd : ℂ → ℝ), 0 < δ ∧ Tendsto Dd (𝓝 t0) (𝓝 0) ∧ ∀ t : ℂ, dist t t0 < δ → t ≠ 0 ∧
          JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε' (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a) ∧
          B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a) Kb ∧
          JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε'
            (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a - PBE.xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc t0) h a) ∧
          B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N)
            (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a - PBE.xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc t0) h a) (Dd t) := by
  obtain ⟨Cs, hCs0, hCs⟩ := sliceContQa
  refine ⟨Cs, hCs0, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi w hw h0 m hc hpb hm hsz t0 ht0
  have H := fun a : Wd.Ix (Fin w.length) =>
    hCs Cc hCc k r Wp Wq T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi w hw h0 m hc hpb hm hsz t0 ht0 a
  choose ef hef hP using H
  refine ⟨Finset.univ.inf' Finset.univ_nonempty ef,
    (Finset.lt_inf'_iff Finset.univ_nonempty).2 (fun a _ => hef a), fun a hh c hsm hcl => ?_⟩
  have hle : Finset.univ.inf' Finset.univ_nonempty ef ≤ ef a := Finset.inf'_le _ (Finset.mem_univ a)
  obtain ⟨δ, Kb, Dd, hδ, hDd, hn⟩ := hP a hh c hsm hcl
  refine ⟨δ, Kb, Dd, hδ, hDd, fun t ht => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hn t ht
  exact ⟨h1, ccCoefM_mono h2 hle, h3, ccCoefM_mono h4 hle, h5⟩

end Formalism.FourierDecayAlt.P.LastBlockContinuity
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.HermitianCurvature.HermitianCurvatureProofs.CcCoefMMono =====
