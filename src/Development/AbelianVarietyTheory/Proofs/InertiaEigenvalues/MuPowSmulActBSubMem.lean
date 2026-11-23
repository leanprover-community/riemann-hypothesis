module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRootsStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem muPow_smul_actB_sub_mem : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (ε : OCb l), IsEps ε → ∀ (k : ℕ) (v : TW (OB l O) T) (z : TW (OA l O) T), toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • v = TWincl (toB l O) T z → ∃ z' : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • (actB (sQ l) T g v - v) = TWincl (toB l O) T z' := by
  intro l _ O K _ _ _ _ _ _ _ _ _ T g ε hε k v z hv
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨-, -, -, -, -, hgal, -⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ
  obtain ⟨u, hu⟩ := hgal (sQ l g)
  have hB : ∀ x : OA l O, toB l O (galOA O (sQ l g) x) = galOB O (sQ l g) (toB l O x) := fun x => by
    simp only [toB, AlgHom.comp_apply, galOB_toOB, galOCr_toOCr]
  have hμ : galOA O (sQ l g) ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) =
      ((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k * ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) := by
    rw [map_pow, galOA_tmul, hu, ← mul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hinv : ((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k * ((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k = 1 := by
    rw [← mul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, ← Algebra.TensorProduct.one_def, one_pow]
  set m := toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) with hm
  set w := TWact (galOA O (sQ l g)) T g z with hw
  have h1 : actB (sQ l) T g (m • v) = TWincl (toB l O) T w := by
    rw [hv]
    exact (GlobalTheory.Cyc.Decomp.TWincl_act (toB l O) (galOA O (sQ l g)) (galOB O (sQ l g)) hB T g z).symm
  have h2 : actB (sQ l) T g (m • v) =
      toB l O (((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k) • (m • actB (sQ l) T g v) := by
    rw [actB, GlobalTheory.Cyc.Decomp.TWact_smul, hm, ← hB, hμ, map_mul, mul_smul]
  have h3 : m • actB (sQ l) T g v =
      TWincl (toB l O) T ((((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k) • w) := by
    rw [GlobalTheory.Cyc.Decomp.TWincl_smul, ← h1, h2, smul_smul, ← map_mul, hinv, map_one, one_smul]
  refine ⟨(((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k) • w - z, ?_⟩
  rw [smul_sub, h3, hv, map_sub]

end GlobalTheory.BKGal
