module

public import Development.EtaleCohomology.EtaleSheaves.AlgResPropsPf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory LateralTheory.E.t_E3Cut

namespace LateralTheory.E.EtAlgPf

theorem key (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B] (Q : Ideal B) [Q.IsPrime]
    (c : B) : ∃ p : Polynomial A, (∃ n, algebraMap A B (p.coeff n) ∉ Q) ∧ p.eval₂ (algebraMap A B) c ∈ Q := by
  let P := Q.comap (algebraMap A B)
  have : Q.LiesOver P := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver P Q
  have : Algebra.IsUnramifiedAt A Q := inferInstance
  have : Module.Finite P.ResidueField Q.ResidueField := inferInstance
  have : IsScalarTower A P.ResidueField Q.ResidueField := inferInstance
  set x := algebraMap B Q.ResidueField c
  have hx : IsIntegral P.ResidueField x := Algebra.IsIntegral.isIntegral x
  let p := minpoly P.ResidueField x
  have hp0 : p ≠ 0 := minpoly.ne_zero hx
  let M := nonZeroDivisors (A ⧸ P)
  let q := IsLocalization.integerNormalization M p
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_spec M p
  have hq0 : q ≠ 0 := by
    intro h; exact hp0 ((IsLocalization.integerNormalization_eq_zero_iff le_rfl p).1 h)
  have hqm : q.map (algebraMap (A ⧸ P) P.ResidueField) = Polynomial.C (algebraMap (A ⧸ P) P.ResidueField b) * p := by
    rw [hb.2, ← Polynomial.smul_eq_C_mul, algebraMap_smul]
  obtain ⟨r, hr⟩ := Polynomial.map_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective q
  obtain ⟨n, hn⟩ : ∃ n, q.coeff n ≠ 0 := by
    by_contra h; push_neg at h; exact hq0 (Polynomial.ext h)
  refine ⟨r, ⟨n, ?_⟩, ?_⟩
  · intro hm; apply hn
    rw [← hr, Polynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem]; exact hm
  · rw [← Ideal.algebraMap_residueField_eq_zero, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq]
    have e1 : algebraMap A Q.ResidueField = (algebraMap P.ResidueField Q.ResidueField).comp
        ((algebraMap (A ⧸ P) P.ResidueField).comp (Ideal.Quotient.mk P)) := by
      ext a
      rw [RingHom.comp_apply, RingHom.comp_apply, ← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply A (A ⧸ P) P.ResidueField,
        ← IsScalarTower.algebraMap_apply A P.ResidueField Q.ResidueField]
    rw [e1, ← Polynomial.eval₂_map, ← Polynomial.map_map, hr, hqm, ← Polynomial.aeval_def, map_mul,
      minpoly.aeval, mul_zero]

theorem EtAlg_of : LateralTheory.E.AlgResPropsPf.EtAlg := by
  intro A B f hf
  let _ := f.hom.toAlgebra
  have : Algebra.Etale A B := hf
  intro Q hQ c
  exact key A B Q c

end LateralTheory.E.EtAlgPf
