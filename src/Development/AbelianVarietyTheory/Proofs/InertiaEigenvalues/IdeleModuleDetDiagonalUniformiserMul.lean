module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddHaarMapMulFiniteIdeleOfUniformizerPowers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.CellDec.DetMod

theorem prod_adl {E : Type} [Field E] [NumberField E] {ι : Type} (s : Finset ι)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m : ι → HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    ∏ i ∈ s, GlobalTheory.CellDec.adl ϖ (m i) = GlobalTheory.CellDec.adl ϖ (∑ i ∈ s, m i) := by
  induction s using Finset.induction_on with
  | empty => simp [GlobalTheory.CellDec.adl_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, GlobalTheory.CellDec.adl_add]

theorem det_finGL' {E : Type} [Field E] [NumberField E] {a : ℕ} (k : GL (Fin a) (Af E)) :
    GeneralLinearGroup.det (finGL E a k) = finId E (GeneralLinearGroup.det k) := by
  let p : Ad E →+* InfiniteAdeleRing E := RingHom.fst (InfiniteAdeleRing E) (Af E)
  refine Units.ext (Prod.ext ?_ ?_)
  · have h := GlobalTheory.CuspRep.det_map p (finGL E a k)
    have h0 : GeneralLinearGroup.map p (finGL E a k) = 1 :=
      map_cornerGL_of_zero (sFin E) p (fun x => rfl) k
    rw [h0, map_one, Units.val_one] at h
    change p _ = _
    rw [← h]
    change (1 : InfiniteAdeleRing E) = (1 : InfiniteAdeleRing E) - 0 + 0
    simp
  · have h := GlobalTheory.CuspRep.det_map (pFin E) (finGL E a k)
    have h0 : GeneralLinearGroup.map (pFin E) (finGL E a k) = GeneralLinearGroup.map (RingHom.id _) k :=
      map_cornerGL_of_hom (sFin E) (pFin E) (RingHom.id _) (fun x => rfl) k
    rw [h0] at h
    change pFin E _ = _
    rw [← h]
    change _ = (1 : Af E) - 1 + (GeneralLinearGroup.det k : (Af E)ˣ)
    rw [sub_self, zero_add]
    rfl

end GlobalTheory.CellDec.DetMod

theorem GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ),
    (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n),
      (ideleModule E (GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l * g)) : ℝ) =
        (∏ v ∈ l.support, ((qV E v : ℝ) ^ (∑ i, l v i))⁻¹) * (ideleModule E (GeneralLinearGroup.det g) : ℝ) := by
  intro E _ _ n ϖ hϖ l g
  rw [map_mul, map_mul, Positive.val_mul]
  congr 1
  have hdet : GeneralLinearGroup.det (GlobalTheory.SmGL.diagT (Af E) (Fin n)
      fun i => GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l)) =
      ∏ i, GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, GlobalTheory.SmGL.val_diagT, Matrix.det_diagonal, Units.coe_prod]
  unfold GlobalTheory.CellDec.tl
  rw [GlobalTheory.CellDec.DetMod.det_finGL', hdet, GlobalTheory.CellDec.DetMod.prod_adl]
  rw [GlobalTheory.AdeleScale.ideleModule_finId_adl ϖ hϖ _ l.support]
  · refine Finset.prod_congr rfl fun v _ => ?_
    congr 2
    rw [Finsupp.finsetSum_apply]
    rfl
  · intro v hv
    rw [Finsupp.notMem_support_iff] at hv
    rw [Finsupp.finsetSum_apply]
    simp [hv]
