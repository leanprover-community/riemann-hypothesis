module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfOrthoB
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU
  PI.OmLocU.Orb
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def ExtP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  ∀ h : a ≤ n, GoodP σ J ψ v Λ a Y → ∃ G : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
    ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
    ∃ Z : Fin n → Fin n → Fv F v ⊗[F] E, IsOBas v Λ Z ∧ (∀ i, Z (eSp h (Sum.inl i)) = X i) ∧
      gramR (Fv F v) σ J Z = G ∧ IsUnit (colM v Z).det

theorem orbP_of (a : ℕ) (Y : TupV (E := E) v n a) (hE : ExtP σ J ψ v Λ a Y) :
    OrbP σ J ψ v Λ a Y := by
  intro hG X hX hXY
  have h : a ≤ n := hG.2.2.2.2.1
  obtain ⟨G, hGe⟩ := hE h hG
  obtain ⟨ZX, hbX, heX, hgX, hdX⟩ := hGe X hX hXY
  obtain ⟨ZY, hbY, heY, hgY, hdY⟩ := hGe Y hG.2.2.2.2.2 rfl
  set uX := Matrix.nonsingInvUnit (colM v ZX) hdX with huX
  set uY := Matrix.nonsingInvUnit (colM v ZY) hdY with huY
  set k : GL (Fin n) (Fv F v ⊗[F] E) := uX * uY⁻¹ with hk
  have hkY : (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * colM v ZY = colM v ZX := by
    have : k * uY = uX := by rw [hk, inv_mul_cancel_right]
    exact congrArg Units.val this
  have hYN : colM v ZY * ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 1 := by
    have : uY * uY⁻¹ = 1 := mul_inv_cancel uY
    exact congrArg Units.val this
  have hkval : (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = colM v ZX * ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := rfl
  have hgXY : cT (sigR (Fv F v) σ) (colM v ZX) * JR (Fv F v) J * colM v ZX =
      cT (sigR (Fv F v) σ) (colM v ZY) * JR (Fv F v) J * colM v ZY := by
    rw [← gram_eq_colM, ← gram_eq_colM, hgX, hgY]
  have hkU : k ∈ HR (Fv F v) σ J := by
    show cT (sigR (Fv F v) σ) (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * JR (Fv F v) J * (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) =
      JR (Fv F v) J
    rw [hkval]
    set N := ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    calc cT (sigR (Fv F v) σ) (colM v ZX * N) * JR (Fv F v) J * (colM v ZX * N)
        = cT (sigR (Fv F v) σ) N * (cT (sigR (Fv F v) σ) (colM v ZX) * JR (Fv F v) J * colM v ZX) * N := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT (sigR (Fv F v) σ) N * (cT (sigR (Fv F v) σ) (colM v ZY) * JR (Fv F v) J * colM v ZY) * N := by
          rw [hgXY]
      _ = cT (sigR (Fv F v) σ) (colM v ZY * N) * JR (Fv F v) J * (colM v ZY * N) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = JR (Fv F v) J := by rw [hYN, cT_one, Matrix.one_mul, Matrix.mul_one]
  let g : HA (Fv F v) σ J := (⟨k, hkU⟩ : ↥(HR (Fv F v) σ J))
  have hgm : ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := rfl
  have hinv : ((k⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 1 :=
    congrArg Units.val (inv_mul_cancel k)
  refine ⟨g, ?_, ?_⟩
  · show ∀ x, x ∈ latLoc (E := E) v Λ ↔
      Matrix.mulVec ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x ∈ latLoc (E := E) v Λ
    intro x
    rw [hgm]
    constructor
    · intro hx
      obtain ⟨c, hc, rfl⟩ := (hbY x).1 hx
      refine (hbX _).2 ⟨c, hc, ?_⟩
      rw [sum_eq_colM, sum_eq_colM, mulVec_mulVec, hkY]
    · intro hx
      obtain ⟨c, hc, hxc⟩ := (hbX _).1 hx
      refine (hbY x).2 ⟨c, hc, ?_⟩
      rw [sum_eq_colM] at hxc ⊢
      rw [← hkY, ← mulVec_mulVec] at hxc
      have := congrArg (fun y => ((k⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y) hxc
      simpa only [mulVec_mulVec, ← Matrix.mul_assoc, hinv, one_mulVec, Matrix.one_mul] using this
  · funext i
    show X i = ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Y i
    rw [hgm, ← heX i, ← heY i, col_eq_colM v ZX, col_eq_colM v ZY, mulVec_mulVec, hkY]

end PI.OmVd
