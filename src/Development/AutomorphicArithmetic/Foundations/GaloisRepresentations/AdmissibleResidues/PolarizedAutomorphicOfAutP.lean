module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base

namespace UpperTheory.GalN.V

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}

theorem Wit.iso' [IsCMField F] (e : RepIso r r') (hU : Wit ι r) : Wit ι r' := by
  intro w hw A hA hfin
  obtain ⟨g, hg⟩ := e
  have hfin' : (r '' (Ine (F := F) A : Set (G F Ω))).Finite := by
    refine (hfin.image (fun x => g⁻¹ * x * g)).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨r' s, ⟨s, hs, rfl⟩, ?_⟩
    simp only [hg s]
    group
  obtain ⟨s, j, hj, hF, h⟩ := hU w hw A hA hfin'
  refine ⟨s, j, hj, hF, fun α β hα hβ k hk => ?_⟩
  rw [hg s, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at hα hβ
  exact h α β hα hβ k hk

theorem attC_iso [_root_.NumberField.IsTotallyComplex F] {π : CuspSub F n} (h : RepIso r r') (H : AttC ι r π) : AttC ι r' π := by
  refine ⟨?_, H.2.mono fun _ ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩
  obtain ⟨g, hg⟩ := h
  let e : (Fin n → Qbar l) ≃ₗ[Qbar l] (Fin n → Qbar l) :=
    Matrix.toLin'OfInv (M := (g : Matrix (Fin n) (Fin n) (Qbar l)))
      (M' := ((g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)))
      (Units.mul_inv g) (Units.inv_mul g)
  have he (v : Fin n → Qbar l) :
      e v = ((g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v := rfl
  have intertwine (s : G F Ω) (v : Fin n → Qbar l) :
      e ((r' s : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v) =
        (r s : Matrix (Fin n) (Fin n) (Qbar l)).mulVec (e v) := by
    rw [he, he, hg s, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  intro W hW
  obtain ⟨W', hW', hc⟩ := H.1 (W.map e.toLinearMap) (by
    rintro s _ ⟨v, hv, rfl⟩
    exact ⟨_, hW s v hv, intertwine s v⟩)
  refine ⟨W'.comap e.toLinearMap, fun s v hv => ?_, ?_⟩
  · show e _ ∈ W'
    rw [intertwine]
    exact hW' s (e v) hv
  · have hcompl : IsCompl ((W.map e.toLinearMap).comap e.toLinearMap) (W'.comap e.toLinearMap) :=
      (Submodule.orderIsoMapComap e).symm.isCompl hc
    rwa [Submodule.comap_map_eq_of_injective e.injective] at hcompl

theorem autCsd_iso {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : Af.RepIso r r')
    (H : IsAutCsdN ι r) : IsAutCsdN ι r' :=
  ⟨H.1.imp fun _ k => ⟨k.1, k.2.1, attC_iso h k.2.2⟩, fun c => (H.2 (continuous_of_iso c h.symm')).iso' h⟩

end

def NewformAut0 : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (f : Newform k) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (j : ℤ), f.Att ι (tw W (cycBar ℚ Ω l ^ j)) → IsAutomorphicOverImagQuad ι W

end UpperTheory.GalN.V
