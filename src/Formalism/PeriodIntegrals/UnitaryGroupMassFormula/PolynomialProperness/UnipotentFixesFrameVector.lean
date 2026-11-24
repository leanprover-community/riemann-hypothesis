module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.UnitriangularInversePolynomialBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.PolynomialProperness

lemma one_mem_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · show (1 : B.Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  · simp
  · simp
  · simp

lemma UW_fix {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z)
    (b : Fin (r + 1)) : h *ᵥ fvec k r z b = fvec k r z b := by
  unfold fvec
  split_ifs with hb
  · exact (hh.2.1 _).1
  · exact hh.2.2

lemma unipotent_fixes_frame_vector (hU : UMapFrame) {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : StdZ k r z)
    {n0 : B.Mat k r} (hn : n0 ∈ N0set k r z) (b : Fin (r + 1)) :
    n0 *ᵥ fvec k r z b = fvec k r z b := by
  have hS : n0 ∈ Sset k r z := ⟨1, one_mem_UW k r z, n0, hn.1, (Matrix.one_mul _).symm⟩
  rw [((hU k r z hz).1 n0 hS).1 b, hn.2]
  simp [Matrix.one_apply]

lemma sg_frame (hU : UMapFrame) (hT : TauMem) (hG : GVGroup) {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} (hz : StdZ k r z) {n0 h : B.Mat k r}
    {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hn : n0 ∈ N0set k r z) (hv : v ∈ UTset (r + 1)) (hh : h ∈ UWset k r z) :
    n0 * tauM k r z v * h ∈ B.GV k r ∧
      ∀ b, (n0 * tauM k r z v * h) *ᵥ fvec k r z b = fmul k r z v b := by
  obtain ⟨hτN, hτf, -⟩ := hT k r z hz v hv
  have hmul := (hG k r).1
  refine ⟨hmul _ (hmul _ hn.1.1 _ hτN.1) _ hh.1, fun b => ?_⟩
  rw [← Matrix.mulVec_mulVec, UW_fix hh, ← Matrix.mulVec_mulVec, hτf b]
  simp only [fmul, Matrix.mulVec_sum, Matrix.mulVec_smul, unipotent_fixes_frame_vector hU hz hn]

theorem frameS_of (hU : UMapFrame) (hG : GVGroup) : FrameS := by
  intro k r z hz s hs
  have hs' := hs
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  obtain ⟨hf, hut, -⟩ := (hU k r z hz).1 _ hs'
  exact ⟨(hG k r).1 _ hh.1 _ hm.1, uMap k r z (h * m), hut, hf⟩

theorem frameSg_of (hU : UMapFrame) (hT : TauMem) (hG : GVGroup) : FrameSg := by
  intro k r z z' γ hstd σ hσ
  obtain ⟨n0, hn, v, hv, hvL, h, hh, rfl⟩ := hσ
  obtain ⟨h1, h2⟩ := sg_frame hU hT hG hstd.2.1 hn hv hh
  exact ⟨h1, v, hv, hvL, h2⟩

theorem frameSg'_of (hU : UMapFrame) (hT : TauMem) (hG : GVGroup) : FrameSg' := by
  intro k r z z' γ hstd σ hσ
  obtain ⟨n0, hn, v, hv, hPv, h, hh, rfl⟩ := hσ
  obtain ⟨h1, h2⟩ := sg_frame hU hT hG hstd.2.2 hn hv hh
  exact ⟨h1, v, hv, hPv, h2⟩

end PI.PolynomialProperness
