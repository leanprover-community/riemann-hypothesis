module

public import Development.EtaleCohomology.CohomologicalPurity.LeafExcSpPf
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
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

@[expose] public section

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem isIso_cokMap_f {R : Type} [CommRing R] {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (comm : f ≫ b = a ≫ f') (n : ℤ)
    (h : IsIso (cokernel.map (f.f n) (f'.f n) (a.f n) (b.f n) (sqw comm n).symm)) : IsIso ((cokernel.map f f' a b comm.symm).f n) := by
  let E := HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) n
  let e1 : (cokernel f).X n ≅ cokernel (f.f n) := PreservesCokernel.iso E f
  let e2 : (cokernel f').X n ≅ cokernel (f'.f n) := PreservesCokernel.iso E f'
  have h1 : (cokernel.π f).f n ≫ e1.hom = cokernel.π (f.f n) := PreservesCokernel.π_iso_hom E f
  have h2 : (cokernel.π f').f n ≫ e2.hom = cokernel.π (f'.f n) := PreservesCokernel.π_iso_hom E f'
  have hep : Epi ((cokernel.π f).f n) := by
    have e : (cokernel.π f).f n = cokernel.π (f.f n) ≫ e1.inv := by
      rw [← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [e]; infer_instance
  have key : (cokernel.map f f' a b comm.symm).f n ≫ e2.hom = e1.hom ≫ cokernel.map (f.f n) (f'.f n) (a.f n) (b.f n) (sqw comm n).symm := by
    rw [← cancel_epi ((cokernel.π f).f n), reassoc_of% h1, ← HomologicalComplex.comp_f_assoc]
    simp [cokernel.map, h2]
  have key' : (cokernel.map f f' a b comm.symm).f n = e1.hom ≫ cokernel.map (f.f n) (f'.f n) (a.f n) (b.f n) (sqw comm n).symm ≫ e2.inv := by
    rw [← Category.assoc, ← key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [key']; infer_instance

theorem shortExact_cok {R : Type} [CommRing R] {K L : Cx R} (f : K ⟶ L) (hf : ∀ n, Mono (f.f n)) :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact := by
  have : Mono f := HomologicalComplex.mono_of_mono_f _ hf
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)) inferInstance inferInstance

theorem leafConeCok_of : LeafConeCok := by
  intro R _ K L K' L' f f' a b comm hf hf' hc
  let S1 := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let S2 := ShortComplex.mk f' (cokernel.π f') (cokernel.condition f')
  let φ : S1 ⟶ S2 := ⟨a, b, cokernel.map f f' a b comm.symm, comm.symm, by simp [S1, S2]⟩
  have q1 := mappingCone.quasiIso_descShortComplex (shortExact_cok f hf)
  have q2 := mappingCone.quasiIso_descShortComplex (shortExact_cok f' hf')
  have hcomp : ∀ n, IsIso (φ.τ₃.f n) := fun n => isIso_cokMap_f f f' a b comm n (hc n)
  have : IsIso φ.τ₃ := HomologicalComplex.Hom.isIso_of_components _
  have hm := mappingCone.map_descShortComplex S1 S2 φ
  have : QuasiIso (mappingCone.descShortComplex S1 ≫ φ.τ₃) := inferInstance
  have : QuasiIso (mappingCone.map f f' a b comm ≫ mappingCone.descShortComplex S2) := by
    change QuasiIso (mappingCone.map S1.f S2.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm ≫ mappingCone.descShortComplex S2)
    rw [hm]; infer_instance
  exact (quasiIso_iff_comp_right _ (mappingCone.descShortComplex S2)).1 this

end LateralTheory.CohomologicalPurity.Thom.ExcSp
