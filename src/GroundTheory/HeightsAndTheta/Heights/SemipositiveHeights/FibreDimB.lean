module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace FibreDimB

theorem trdeg_eq_of_isFractionRing (B : Type) [CommRing B] [IsDomain B] (L : Type) [Field L] [Algebra B L]
    [IsFractionRing B L] (hB : Function.Injective (algebraMap ℤ B)) :
    Algebra.trdeg ℤ L = Algebra.trdeg ℤ B := by
  have : FaithfulSMul B L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective B L)
  have : FaithfulSMul ℤ B := (faithfulSMul_iff_algebraMap_injective _ _).2 hB
  have : Algebra.IsAlgebraic B L := IsLocalization.isAlgebraic L (nonZeroDivisors B)
  rw [← trdeg_add_eq ℤ B (A := L), trdeg_eq_zero (R := B) (A := L), add_zero]

theorem trdeg_eq_of_gen {σ L : Type} [Field L] (y : σ → L) (P : Ideal (MvPolynomial σ ℤ))
    (hker : RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L) = P)
    (hZ : Function.Injective (algebraMap ℤ L))
    (hgen : ∀ z : L, ∃ f g : MvPolynomial σ ℤ, z = aeval y f / aeval y g) :
    Algebra.trdeg ℤ L = Algebra.trdeg ℤ (MvPolynomial σ ℤ ⧸ P) := by
  subst hker
  set φ := Ideal.kerLiftAlg (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L) with hφdef
  have : (RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L)).IsPrime := RingHom.ker_isPrime _
  let _ : Algebra (MvPolynomial σ ℤ ⧸ RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L)) L :=
    φ.toRingHom.toAlgebra
  have hφ : Function.Injective φ := Ideal.kerLiftAlg_injective _
  have : FaithfulSMul (MvPolynomial σ ℤ ⧸ RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L)) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : IsFractionRing (MvPolynomial σ ℤ ⧸ RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L)) L :=
    IsFractionRing.of_field _ L fun z => by
      obtain ⟨f, g, rfl⟩ := hgen z
      exact ⟨Ideal.Quotient.mk _ f, Ideal.Quotient.mk _ g, (congrArg₂ (· / ·) (Ideal.kerLiftAlg_mk (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L) f)
        (Ideal.kerLiftAlg_mk (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] L) g)).symm⟩
  refine trdeg_eq_of_isFractionRing _ L fun a b h => hZ ?_
  simpa only [eq_intCast, map_intCast] using congrArg φ h

theorem trdeg_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {n : ℕ} (hP : IsArithVar P n) :
    ∃ t : ℕ, Algebra.trdeg ℤ (MRing ι ⧸ P) = t ∧ t + 1 = n + Fintype.card K := by
  obtain ⟨_, ⟨hprime, -, -⟩, hhor, hdim⟩ := hP
  have := hprime
  have hA := IntDomainDim.proof (MRing ι ⧸ P) (CoordinateConeArithVar.algebraMap_injective P hhor)
  rw [hdim] at hA
  have h' : ((n + Fintype.card K : ℕ) : ℕ∞) = (Algebra.trdeg ℤ (MRing ι ⧸ P)).toENat + 1 := by
    exact_mod_cast hA
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (Algebra.trdeg ℤ (MRing ι ⧸ P)).toENat = t := by
    refine ENat.ne_top_iff_exists.mp (fun htop => ?_) |>.imp fun _ h => h.symm
    rw [htop] at h'
    simp at h'
  refine ⟨t, Cardinal.toENat_eq_natCast.mp ht, ?_⟩
  rw [ht] at h'
  exact_mod_cast h'.symm

theorem aeval_mem_closure {σ L : Type} [Field L] (y : σ → L) (f : MvPolynomial σ ℤ) :
    aeval y f ∈ Subfield.closure (Set.range y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [intCast_mem]
  | add f g hf hg => simpa using add_mem hf hg
  | mul_X f i hf => simpa using mul_mem hf (Subfield.subset_closure ⟨i, rfl⟩)

end FibreDimB


section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.ForSecondHalf
