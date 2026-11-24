module

public import GroundTheory.AutomorphicForms.GL2.GJGlobalDefs
public import GroundTheory.AutomorphicForms.GL2.GJMatrixSchwartz
public import GroundTheory.AutomorphicForms.GL2.GJGlobalLatticeCont
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open GJMatrix

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem summable_norm_ratMat {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) (t : {r : ℝ // 0 < r}) (a b : AdelicGLn.AdelicGL K n) :
    Summable (fun ξ : Matrix (Fin n) (Fin n) K => ‖Φ (((Reduction.centralSection K n t * a :
      AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        (b : Matrix (Fin n) (Fin n) 𝔸[K]))‖) := by
  obtain ⟨u, hu, hbd⟩ := exists_summable_bound hΦ t (isCompact_singleton (x := a))
    (isCompact_singleton (x := b))
  exact hu.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun ξ => hbd t le_rfl a rfl b rfl ξ)

end GJGlobal

end

end GroundTheory.Automorphic
