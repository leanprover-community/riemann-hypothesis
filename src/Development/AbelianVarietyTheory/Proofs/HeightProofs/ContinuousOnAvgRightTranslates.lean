module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.AvgCont

theorem isClosed_UJset {n : ℕ} (ε : Fin n → Bool) : IsClosed (UJset ε) := by
  show IsClosed {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε}
  refine isClosed_eq ?_ continuous_const
  exact ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id

theorem mul_mem_UJset_of_inUJ {n : ℕ} {ε : Fin n → Bool} {y m : Matrix (Fin n) (Fin n) ℂ}
    (hy : y ∈ UJset ε) (hm : Formalism.REAL.inUJ ε m) : y * m ∈ UJset ε := by
  have hy' : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε := hy
  have hm' : mᴴ * Formalism.REAL.Jm ε * m = Formalism.REAL.Jm ε := hm
  show (y * m)ᴴ * Formalism.REAL.Jm ε * (y * m) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul]
  calc mᴴ * yᴴ * Formalism.REAL.Jm ε * (y * m) = mᴴ * (yᴴ * Formalism.REAL.Jm ε * y) * m := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hy', hm']

theorem continuous_maximalCompactSubgroup_toMatrix {n : ℕ} (ε : Fin n → Bool) :
    Continuous (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) :=
  Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuousOn_avg_right_translates : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ),
    ContinuousOn f (UJset ε) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) := by
  intro n ε f hf e he
  rw [continuousOn_iff_continuous_restrict]
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : FirstCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (UJset ε) :=
    (isClosed_UJset ε).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let F : UJset ε → Formalism.REAL.KG ε → ℂ := fun y k => e k * f ((y : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.toMK k)
  have hF : Continuous (Function.uncurry F) := by
    refine (he.comp continuous_snd).mul ?_
    have hmaps : ∀ p : UJset ε × Formalism.REAL.KG ε,
        (p.1 : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.toMK p.2 ∈ UJset ε :=
      fun p => mul_mem_UJset_of_inUJ p.1.2 ((p.2 : Formalism.REAL.UJ ε).2)
    exact hf.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).matrix_mul
        ((continuous_maximalCompactSubgroup_toMatrix ε).comp continuous_snd)) hmaps
  have h := continuous_parametric_integral_of_continuous (μ := Formalism.REAL.muK ε) hF isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h

end GlobalTheory.AvgCont
