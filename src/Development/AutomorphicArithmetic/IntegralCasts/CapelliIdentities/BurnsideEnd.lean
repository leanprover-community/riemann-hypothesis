module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.Reformulated.B.Qj3.burnside_end.{u_3, u_4} :
    ∀ {K : Type u_3} {V : Type u_4} [inst : Field K] [IsAlgClosed K] [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module K V] [FiniteDimensional K V] (S : Subalgebra K (Module.End K V)),
    (∀ (N : Submodule K V), (∀ f ∈ S, ∀ v ∈ N, (f : V → V) v ∈ N) → N = ⊥ ∨ N = ⊤) → ∀ (f : Module.End K V), f ∈ S := by
  intro K V _ _ _ _ _ S h f
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : f = 0 := by ext v; exact Subsingleton.elim _ _
    rw [this]; exact S.zero_mem
  haveI : IsSimpleModule S V := by
    refine { eq_bot_or_eq_top := fun N => ?_ }
    rcases h (N.restrictScalars K) (fun g hg v hv => N.smul_mem (⟨g, hg⟩ : S) hv) with h1 | h1
    · left
      exact (Submodule.restrictScalars_eq_bot_iff _ _ _).1 h1
    · right
      exact (Submodule.restrictScalars_eq_top_iff _ _ _).1 h1
  have hs := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K (A := S) (V := V)).2
  let F : Module.End (Module.End S V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, rfl⟩ := hs φ
        simp [Module.End.smul_def, Module.algebraMap_end_apply] }
  classical
  let b := Module.finBasis K V
  obtain ⟨r, hr⟩ := jacobson_density (R := S) F (Finset.univ.image b)
  have : f = (r : Module.End K V) := by
    refine b.ext fun i => ?_
    exact hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [this]; exact r.2
