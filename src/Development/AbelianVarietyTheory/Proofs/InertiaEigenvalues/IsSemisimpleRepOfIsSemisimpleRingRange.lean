module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.MainNotions.N

namespace GlobalTheory

theorem isSSRep_of_isSemisimpleRing_range :
    ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k),
      IsSemisimpleRing ρ.range → IsSSRep ((ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits) := by
  intro Γ k _ _ d ρ hss W hW

  have hB : ∀ x : MonoidAlgebra k Γ, ∀ v ∈ W, (ρ x).mulVec v ∈ W := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g => intro v hv; exact hW g v hv
    | add x y hx hy =>
      intro v hv; rw [map_add (f := _), Matrix.add_mulVec]; exact W.add_mem (hx v hv) (hy v hv)
    | smul c x hx =>
      intro v hv; rw [map_smul, Matrix.smul_mulVec]; exact W.smul_mem c (hx v hv)
  let WB : Submodule ρ.range (Fin d → k) :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := by
        rintro ⟨b, x, rfl⟩ v hv
        exact hB x v hv }
  have hWB : WB.restrictScalars k = W := by ext v; rfl
  obtain ⟨WB', hc⟩ := exists_isCompl WB
  refine ⟨WB'.restrictScalars k, ?_, ?_⟩
  · intro g v hv
    have hmem : ρ (MonoidAlgebra.of k Γ g) ∈ ρ.range := ⟨_, rfl⟩
    exact WB'.smul_mem ⟨_, hmem⟩ hv
  · rw [← hWB]
    exact hc.map (Submodule.restrictScalarsLatticeHom k ρ.range (Fin d → k))

end GlobalTheory
