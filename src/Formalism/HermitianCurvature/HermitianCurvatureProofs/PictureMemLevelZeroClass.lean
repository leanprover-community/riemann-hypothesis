module

public import Formalism.HermitianCurvature.StatementJC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairAtStarMul

@[expose] public section

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section Tower

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P0 : M.Par} {T : D.LevTower P0.k P0.r Wp Wq} {j : Fin (P0.r + 1)}

def IsPic (T : D.LevTower P0.k P0.r Wp Wq) (j : Fin (P0.r + 1))
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ y ∈ DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
    (Φ : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (B.JF (T.bs j) F) y.1 y.2

theorem radSp_ext {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (Φ Ψ : RadSp k r z z' π π')
    (h : ∀ y ∈ DomR k r z z', (Φ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = (Ψ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2) : Φ = Ψ := by
  apply Subtype.ext
  funext c g
  by_cases hy : ((c, g) : (Fin r → ℂ) × Mx k r) ∈ DomR k r z z'
  · exact h _ hy
  · rw [Φ.2.1 (c, g) hy, Ψ.2.1 (c, g) hy]

theorem resG_JF_zero {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (i : Fin (r + 1)) :
    resG k r i (B.JF Bs (fun _ => (0 : Wq →L[ℂ] Wp))) = 0 := by
  funext c g
  simp [resG, Formalism.FourierDecayAlt.P.JCx2.bc_JF_zero]

end Tower

section Cls

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P0 : M.Par} {T : D.LevTower P0.k P0.r Wp Wq} {j : Fin (P0.r + 1)}
  {X : ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
  {μ : MeasureTheory.Measure (Mt (JC.parLev P0 j).k (JC.parLev P0 j).r)}
  {L : R.LevelData (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
      (JC.parLev P0 j).r}
  {st : Fr.Start (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))}
  {l0 : ℕ}
  {K : Fin ((JC.parLev P0 j).r + 1) →
    Submodule ℂ (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')}

end Cls

section Words

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {S : Type}

theorem wordOK_gen (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hOK : P.OK) (hl1 : 1 ≤ l0) (hlk : l0 ≤ P.k) (hq : st.q = M.qC P)
    (hinv : st.inv = {Y | ∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0}) (u : List (Letter ℂ S))
    (hnd : (u.map Letter.intersection_update_fsHerm_neg_one).Nodup) (hpt : ∀ l ∈ u, ∃ Y : ℝ, l.pt = (Y : ℂ) ∧ I.OnCut P.u P.u' l0 Y)
    (hsep : u.Pairwise fun l l' => 2 < |l.pt.re - l'.pt.re|) : WordOK P z z' π π' st l0 u := by
  refine ⟨⟨hnd, ?_, ?_, ?_⟩, ?_, hsep⟩
  · intro l hl
    obtain ⟨Y, e, -⟩ := hpt l hl
    rw [e]; exact Complex.conj_ofReal Y
  · intro l hl
    obtain ⟨Y, e, hc⟩ := hpt l hl
    rw [e]
    have hx : ∀ e : ℝ, -1 ≤ e → e ≤ 1 → ∀ ρ, M.xC P ρ ((Y + e : ℝ) : ℂ) ≠ 0 :=
      fun e h1 h2 ρ => Formalism.FourierDecayAlt.P.JCTx5.xC_ne P hOK l0 hl1 hlk _ hc e h1 h2 ρ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hinv]; intro ρ; simpa using hx 0 (by norm_num) (by norm_num) ρ
    · rw [hinv]; intro ρ; simpa using hx 1 (by norm_num) (by norm_num) ρ
    · rw [hinv]; intro ρ; simpa [sub_eq_add_neg] using hx (-1) (by norm_num) (by norm_num) ρ
    · rw [hq]; simpa using Formalism.FourierDecayAlt.P.JCTx5.qC_ne P hOK l0 hl1 hlk _ hc 0 (by norm_num) (by norm_num)
    · rw [hq]; simpa [sub_eq_add_neg] using Formalism.FourierDecayAlt.P.JCTx5.qC_ne P hOK l0 hl1 hlk _ hc (-1) (by norm_num) (by norm_num)
  · refine hsep.imp fun {l l'} h n hn e => ?_
    have hre : l.pt.re - l'.pt.re = (n : ℝ) := by
      have := congrArg Complex.re e
      simpa using this
    have h2 : |(n : ℝ)| ≤ 2 := by exact_mod_cast hn
    rw [hre] at h
    linarith
  · intro l hl
    obtain ⟨Y, e, hc⟩ := hpt l hl
    rw [e]
    exact ⟨by simp, by simpa using hc⟩

end Words

end

end Formalism.FourierDecayAlt.P.PBF
