module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.AutomorphicFormsLeSm
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelFinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuousStatement
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
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
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermEqZero, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjFiniteUnipotentMemOpenSubgroup, Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormEqZeroOfWhittakerVanishing

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermEqZero =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermEqZero", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd\npublic import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.AutomorphicFormsLeSm\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem IsCuspForm.mem_cuspForms {φ : Sm E a} (h : IsCuspForm φ) : φ.1 ∈ cuspForms E a :=
  (UpperTheory.V.Cm.isCuspForm_iff φ).1 h

theorem IsCuspForm.constantTerm_eq_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (φ : Sm E a) (h : IsCuspForm φ) : AutomorphicForm.IsCuspidal (K := E) (n := a) φ.1 :=
  h.mem_cuspForms.2

end GlobalTheory.CuspRep
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermEqZero =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjFiniteUnipotentMemOpenSubgroup =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjFiniteUnipotentMemOpenSubgroup", "h": "module\n\npublic import GroundTheory.AutomorphicForms.ReductionSiegel\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart\npublic import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds\npublic import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm\npublic import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelFinite\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL\nimport GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting\n\n"}
section -- clump:auto
@[expose] public section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.FinConj

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem finEmb_eq_finGL (E : Type) [Field E] [NumberField E] (a : ℕ) (l : GL (Fin a) (Af E)) :
    finEmb E a l = finGL E a l := by
  have k1 : ∀ (c : Ad E) (x y : Af E), (c - sFin E y + sFin E x).1 = c.1 - 0 + 0 := fun _ _ _ => rfl
  have k2 : ∀ (c : Ad E) (x y : Af E), (c - sFin E y + sFin E x).2 = c.2 - y + x := fun _ _ _ => rfl
  apply (AdelicGLn.prodEquiv E a).injective
  rw [prodEquiv_finEmb]
  refine Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_))
  · rw [AdelicGLn.prodEquiv_apply_fst]
    change (1 : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j = ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (sFin E) ((1 : Matrix (Fin a) (Fin a) (Af E)) i j) + sFin E (l i j)).1
    rw [k1, sub_zero, add_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rfl
    · rfl
  · rw [AdelicGLn.prodEquiv_apply_snd]
    change (l : Matrix (Fin a) (Fin a) (Af E)) i j = ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (sFin E) ((1 : Matrix (Fin a) (Fin a) (Af E)) i j) + sFin E (l i j)).2
    rw [k2, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rw [adele_one_snd, sub_self, zero_add]
    · rw [adele_zero_snd, sub_self, zero_add]

theorem unip_eq_unipGL (E : Type) [Field E] [NumberField E] (a r : ℕ) (z : BlockIx a r → Ad E) :
    (unip z : GA E a) = unipGL z := Units.ext rfl

theorem exists_conj_unip_mem :
    ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ ω : Set (GA E a), IsCompact ω →
    ∃ M : ℕ, 0 < M ∧ ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
      ∀ z : BlockIx a r → Ad E, (∀ p, (z p).1 = 0) →
      (∀ p, ∃ c ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, (z p).2 = (M : Af E) * c) →
      ∃ l ∈ L, (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k)⁻¹ * unip z *
        (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k) = finGL E a l := by
  intro E _ _ a r L hL ω hω
  set U : Subgroup (AdelicGLn.integralFiniteGL E a) := L.comap (AdelicGLn.integralFiniteGL E a).subtype
  have hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL E a)) := hL.preimage continuous_subtype_val
  obtain ⟨M, hM, h⟩ := exists_natCast_conj_unipGL_mem (K := E) (n := a) U hU hω r
  refine ⟨M, hM, fun b hb ρ hρ k hk z hz1 hz2 => ?_⟩
  obtain ⟨u, hu⟩ := h b hb ρ hρ k hk z hz1 hz2
  refine ⟨((u : AdelicGLn.integralFiniteGL E a) : GL (Fin a) (Af E)), u.2, ?_⟩
  rw [unip_eq_unipGL, ← finEmb_eq_finGL]
  exact hu

end GlobalTheory.FinConj
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjFiniteUnipotentMemOpenSubgroup =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormEqZeroOfWhittakerVanishing =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormEqZeroOfWhittakerVanishing", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuousStatement\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd\npublic import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermEqZero\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjFiniteUnipotentMemOpenSubgroup\npublic import GroundTheory.AutomorphicForms.MultiplicityOne.Injective\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory.JSW

theorem eq_zero_of_whit_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsCuspForm φ → (∀ g, GlobalTheory.JSW.whit φ.1 g = 0) → φ = 0 := by
  intro E _ _ _ a φ hφ hW
  have hc : Continuous φ.1 := GlobalTheory.T.automorphicForm_GL_continuous E a φ hφ.1
  have hcusp := _root_.GlobalTheory.CuspRep.IsCuspForm.constantTerm_eq_zero E a φ hφ
  have hl : GroundTheory.Automorphic.AutomorphicForm.IsLeftInvariant (K := E) (n := a) φ.1 :=
    fun γ g => hφ.1.left γ g
  let V : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | finRep E a k φ = φ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hV : ∃ V : OpenSubgroup (GroundTheory.Automorphic.AdelicGLn.FiniteAdelicGL E a),
      ∀ g, ∀ v ∈ V, φ.1 (g * GroundTheory.Automorphic.AutomorphicForm.finEmb E a v) = φ.1 g :=
    ⟨⟨V, hφ.1.level⟩, fun g v hv => by
      rw [GlobalTheory.FinConj.finEmb_eq_finGL]
      have : (finRep E a v φ).1 g = φ.1 g := by rw [show finRep E a v φ = φ from hv]
      exact this⟩
  apply Subtype.ext
  exact GroundTheory.Automorphic.MultiplicityOne.eq_zero_of_whittaker_eq_zero hc hl hcusp hV hW

end GlobalTheory.JSW
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormEqZeroOfWhittakerVanishing =====
