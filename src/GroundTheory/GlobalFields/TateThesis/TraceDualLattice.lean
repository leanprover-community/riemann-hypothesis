module

public import GroundTheory.GlobalFields.TateThesis.TraceFourier
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ENNReal nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero)

theorem coe_traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := rfl

theorem coeToSubmodule_traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =
      Submodule.traceDual ℤ ℚ (I : Submodule (𝓞 K) K) :=
  FractionalIdeal.coe_dual ℤ ℚ I.ne_zero

theorem traceDualIdeal_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K) =
      ((I : FractionalIdeal (𝓞 K)⁰ K) *
        (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  rw [coe_traceDualIdeal, FractionalIdeal.dual_eq_mul_inv,
    coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K), mul_inv, inv_inv, mul_comm]

theorem dualSubmodule_idealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (mixedTraceForm K).dualSubmodule (idealLattice K I) = idealLattice K (traceDualIdeal K I) := by
  set b := basisOfFractionalIdeal K I
  have hdual : (mixedTraceForm K).dualBasis (mixedTraceForm_nondegenerate K)
      (fractionalIdealLatticeBasis K I) = fun i => mixedEmbedding K (b.traceDual i) := by
    rw [LinearMap.BilinForm.dualBasis_eq_iff]
    intro i j
    rw [fractionalIdealLatticeBasis_apply, mixedTraceForm_mixedEmbedding,
      Module.Basis.trace_traceDual_mul]
    split_ifs <;> simp
  have hspan : (Submodule.traceDual ℤ ℚ (I : Submodule (𝓞 K) K)).restrictScalars ℤ =
      Submodule.span ℤ (Set.range b.traceDual) :=
    Submodule.traceDual_span_of_basis ℤ (I : Submodule (𝓞 K) K) b (by
      ext x
      rw [Submodule.restrictScalars_mem, mem_span_basisOfFractionalIdeal]
      rfl)
  ext y
  rw [← span_idealLatticeBasis, LinearMap.BilinForm.dualSubmodule_span_of_basis _
    (mixedTraceForm_nondegenerate K), hdual, mem_idealLattice,
    show Set.range (fun i => mixedEmbedding K (b.traceDual i)) =
      (mixedEmbedding K).toIntAlgHom.toLinearMap '' Set.range b.traceDual by
        rw [← Set.range_comp]; rfl,
    ← Submodule.map_span, Submodule.mem_map, ← hspan]
  simp only [Submodule.restrictScalars_mem, ← coeToSubmodule_traceDualIdeal]
  rfl

theorem mem_idealLattice_traceDualIdeal_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : mixedSpace K) :
    y ∈ idealLattice K (traceDualIdeal K I) ↔
      ∀ x ∈ idealLattice K I, ∃ n : ℤ, mixedTraceForm K y x = n := by
  rw [← dualSubmodule_idealLattice, LinearMap.BilinForm.mem_dualSubmodule]
  simp only [Submodule.mem_one, algebraMap_int_eq, eq_intCast]
  exact forall₂_congr fun _ _ => exists_congr fun _ => eq_comm

theorem covolume_idealLattice_selfDualMeasure (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (idealLattice K I) (selfDualMeasure K) =
      FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) * √|(discr K : ℝ)| := by
  have h := covolume_idealLattice K I
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_idealLattice K I)]
    at h
  have hF : IsAddFundamentalDomain (idealLattice K I)
      (ZSpan.fundamentalDomain (fractionalIdealLatticeBasis K I)) (selfDualMeasure K) :=
    (fundamentalDomain_idealLattice K I).mono Measure.smul_absolutelyContinuous
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF, selfDualMeasure, measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ← measureReal_def, h, ENNReal.toReal_pow, ENNReal.toReal_ofNat, inv_pow]
  field_simp

end

end GroundTheory.Global
