module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
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

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT.LocAE

theorem mem_GLint_of_entries_inv {L : Type} [Field L] {k : ℕ} (O : Subring L) (g : GL (Fin k) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin k) O := by
  have hi : Function.Injective fun A : Matrix (Fin k) (Fin k) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_mem_KL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ x : finU (E := E) (n := n),
    ∀ᶠ w in cofinite, toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w := by
  intro E _ _ _ _ n x
  have h : ∀ y : FiniteAdeleRing (𝓞 E) E, ∀ᶠ w in cofinite, pLoc E w y ∈ Formalism.UG.Ov E w := fun y => y.2
  have h1 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (pFin E (((x : UA E n) : GA E n).val i j)) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h2 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (pFin E ((((x : UA E n) : GA E n))⁻¹.val i j)) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  filter_upwards [h1, h2] with w a b
  have hK : cLoc w (x : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    refine mem_GLint_of_entries_inv _ _ (fun i j => a i j) (fun i j => ?_)
    rw [← map_inv]
    exact b i j
  unfold toSub
  split_ifs with hU
  · exact Subgroup.mem_subgroupOf.2 hK
  · exact one_mem _

end GlobalTheory.BCT.LocAE
