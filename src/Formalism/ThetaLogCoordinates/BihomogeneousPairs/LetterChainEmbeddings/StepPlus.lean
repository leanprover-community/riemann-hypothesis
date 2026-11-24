module

public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PairStep
public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.BiHomPlus
public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.SmulMemOfNorm
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}

theorem sp_midGen_zero (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    midGen p D 0 j jp x = (∏ i, D.Ehat p (r := r) i ^ j i) *
      (ehP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) ^ jp *
        (X (zP D r) ^ D.zPlus * PL p D (List.finRange D.T.t) j jp x)) := by
  have h1 : D.Eplus p (r := r) = ehP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) := rfl
  unfold midGen
  rw [h1]
  simp only [Nat.not_lt_zero, Finset.filter_false, Finset.prod_empty, List.drop_zero, mul_one]
  ring

theorem sp_gen_P (j : Fin D.T.t → ℕ) (jp : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp * Pplus p D jp y =
      (∏ i, D.Ehat p (r := r) i ^ j i) *
      (ehP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) ^ jp *
        tieP (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) (D.LL.deg D.uPos - jp) (D.B - jp) D.zPlus y) := by
  rw [mul_assoc]
  rfl

theorem sp_wU_inj : Function.Injective (wU (r := r) D) := by
  intro c d h
  simp only [wU, Sum.inl.injEq, Prod.mk.injEq] at h
  exact h.2

theorem sp_xi_inj : Function.Injective (xiVar N r D.T.t) := by
  intro c d h
  simp only [xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  exact h.2

end

theorem StepPlus_of : PairStep → LatPlus → PLLin → CommPL → ParamPL → PlusCondition := by
  intro hPS hLP hLin hComm hPar p _ N r _ D a u hB hr hdeg hBa hz hU hu
  have key : ∀ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp → ∀ x ∈ Lat p D (r := r) j jp,
      ((p : ℚ_[p]) ^ u • midGen p D 0 j jp x ∈ MidP p (r := r) D) ∧
      ((p : ℚ_[p]) ^ u • ((∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
        Pplus p D jp (PL p D (List.finRange D.T.t) j jp x)) ∈ Mid p (r := r) D 0) := by
    intro j jp hOK x hx
    obtain ⟨T, hT⟩ := (hLin p N r D (List.finRange D.T.t) j jp).1
    have hcomm : ∀ (m : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]),
        (tieF (wU D) (xiVar N r D.T.t) ^ m) (T y) = T ((tieF (wU D) (xiVar N r D.T.t) ^ m) y) := by
      intro m y
      rw [hT, hT]
      exact (hComm p N r D hB (List.finRange D.T.t) j jp m y).2
    have hps := hPS p (BVar N r D.T.t) r (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) hr
      (fun c => ⟨by simp [wU, zP, scalZ], by simp [xiVar, zP, scalZ]⟩)
      (D.LL.deg D.uPos) D.B D.zPlus (Nat.log p (2 * a)) u
      (fun l => Submodule.map (T.restrictScalars ℤ_[p]) (Lat p D (r := r) j l))
      (by
        rintro l _ ⟨y, hy, rfl⟩ m hm
        rw [LinearMap.restrictScalars_apply, hcomm]
        have hb := biHom_plus (p := p) (D := D) j l y hy
        rw [deg_U hB] at hb
        rw [tieF_pow_apply_eq_zero_of_min_lt (wU D) (xiVar N r D.T.t) sp_wU_inj sp_xi_inj wU_ne_xi hb m hm, map_zero])
      (by
        rintro l m hm _ ⟨y, hy, rfl⟩
        rw [LinearMap.restrictScalars_apply, hcomm, ← map_smul]
        refine ⟨_, hLP p N r D hB hU j l m (Nat.log p (2 * a)) (Nat.log_mono_right ?_) y hy, rfl⟩
        exact le_trans (le_trans hm (min_le_left _ _)) (hdeg _))
      (by
        refine le_trans (Nat.add_le_add_left (Nat.log_mono_right ?_) _) hu
        have := hdeg D.uPos
        omega)
      jp hOK.2 (T x) ⟨x, hx, rfl⟩
    constructor
    · rw [sp_midGen_zero, ← hT, ← mul_smul_comm]
      refine span_map_mem (LinearMap.mulLeft ℚ_[p] (∏ i, D.Ehat p (r := r) i ^ j i)) _ _ ?_ _ hps.1
      rintro _ ⟨l', hl', _, ⟨y, hy, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨j, l', ⟨hOK.1, hl'⟩, y, hy, ?_⟩
      rw [LinearMap.mulLeft_apply, LinearMap.restrictScalars_apply, hT, sp_gen_P,
        hPar p N r D hB (List.finRange D.T.t) j j jp l' y (fun _ _ => rfl)]
    · rw [sp_gen_P, ← hT, ← mul_smul_comm]
      refine span_map_mem (LinearMap.mulLeft ℚ_[p] (∏ i, D.Ehat p (r := r) i ^ j i)) _ _ ?_ _ hps.2
      rintro _ ⟨l', hl', _, ⟨y, hy, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨j, l', ⟨hOK.1, hl'⟩, y, hy, ?_⟩
      rw [LinearMap.mulLeft_apply, LinearMap.restrictScalars_apply, hT, sp_midGen_zero,
        hPar p N r D hB (List.finRange D.T.t) j j jp l' y (fun _ _ => rfl)]
  let S : MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
    (p : ℚ_[p]) ^ u • LinearMap.id
  constructor
  · intro v hv
    refine span_map_mem S _ (MidP p (r := r) D) ?_ v hv
    rintro _ ⟨j, jp, hOK, x, hx, rfl⟩
    exact (key j jp hOK x hx).1
  · intro v hv
    refine span_map_mem S _ (Mid p (r := r) D 0) ?_ v hv
    rintro _ ⟨j, jp, hOK, x, hx, rfl⟩
    exact (key j jp hOK x hx).2

end Formalism.InvariantFactorPaths.KP.LL
