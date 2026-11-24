module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.OverlapG
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Matrix UpperTheory.V.KT

namespace PositivityTheory.KB.LocalOverlapAverage

theorem discr_holds : Discr := by
  unfold Discr
  intro L _ _ N K hK
  have hc : Continuous (fun γ : Sp L N => fun (w : InfinitePlace L) (i j : Fin N) =>
      ((γ w : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) := by
    fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  set S : Set (𝓞 L) := {x | ∀ w : InfinitePlace L, ‖w.embedding (x : L)‖ ≤ C} with hS
  have hSfin : S.Finite := by
    have h0 := Embeddings.finite_of_norm_le L ℂ C
    refine (h0.preimage (Set.injOn_of_injective (f := fun x : 𝓞 L => (x : L))
      RingOfIntegers.coe_injective)).subset ?_
    intro x hx
    refine ⟨RingOfIntegers.isIntegral_coe x, fun φ => ?_⟩
    have h1 := hx (InfinitePlace.mk φ)
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply] at h1
    exact h1
  have hT : (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => S).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => hSfin
  have hU : {A : Matrix.SpecialLinearGroup (Fin N) (𝓞 L) |
      (A : Matrix (Fin N) (Fin N) (𝓞 L)) ∈ Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => S}.Finite :=
    hT.preimage (Set.injOn_of_injective Subtype.val_injective)
  refine (hU.image (MonoidHom.pi fun w => Matrix.SpecialLinearGroup.map (embO w))).subset ?_
  rintro γ ⟨⟨A, rfl⟩, hγK⟩
  refine ⟨A, ?_, rfl⟩
  intro i _ j _ w
  have h2 := hC _ hγK
  have h3 : ‖(fun (w : InfinitePlace L) (i j : Fin N) =>
      ((((MonoidHom.pi fun w => Matrix.SpecialLinearGroup.map (embO w)) A) w :
        Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) w i j‖ ≤ C :=
    (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans ((norm_le_pi_norm _ w).trans h2))
  exact h3

end PositivityTheory.KB.LocalOverlapAverage

end
