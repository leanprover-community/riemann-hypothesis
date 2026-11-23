module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Limits.Sifted
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem widePushout_finiteType_int {J : Type} [Finite J] [Nonempty J] (A B : CommRingCat.{0})
    (g : A ⟶ B) (hB : Algebra.FiniteType ℤ B) :
    Algebra.FiniteType ℤ ((widePushout A (fun _ : J => B) (fun _ => g) : CommRingCat.{0})) := by
  classical
  obtain ⟨s, hs⟩ := hB.out
  set W := widePushout A (fun _ : J => B) (fun _ => g) with hW
  let T : Set W := ⋃ j : J, (WidePushout.ι (fun _ : J => g) j).hom '' (s : Set B)
  have hTfin : T.Finite := Set.finite_iUnion fun j => s.finite_toSet.image _
  let S : Subring W := Subring.closure T
  have hB' : ∀ b : B, b ∈ Subring.closure (s : Set B) := by
    intro b
    have hb : b ∈ Algebra.adjoin ℤ (s : Set B) := hs ▸ Algebra.mem_top
    rw [Algebra.adjoin_int] at hb
    exact hb
  have hmem : ∀ (j : J) (b : B), (WidePushout.ι (fun _ : J => g) j).hom b ∈ S := by
    intro j b
    have hle : (Subring.closure (s : Set B)).map (WidePushout.ι (fun _ : J => g) j).hom ≤ S := by
      rw [RingHom.map_closure]
      exact Subring.closure_mono (Set.subset_iUnion (fun j => (WidePushout.ι (fun _ : J => g) j).hom '' (s : Set B)) j)
    exact hle ⟨b, hB' b, rfl⟩
  let ιS : J → (B ⟶ CommRingCat.of S) := fun j =>
    CommRingCat.ofHom ((WidePushout.ι (fun _ : J => g) j).hom.codRestrict S (hmem j))
  let j₀ : J := Classical.arbitrary J
  have hw : ∀ j : J, g ≫ ιS j = g ≫ ιS j₀ := by
    intro j
    ext a
    change (g ≫ WidePushout.ι (fun _ : J => g) j) a = (g ≫ WidePushout.ι (fun _ : J => g) j₀) a
    rw [WidePushout.arrow_ι (fun _ : J => g) j, WidePushout.arrow_ι (fun _ : J => g) j₀]
  let d : W ⟶ CommRingCat.of S := WidePushout.desc (g ≫ ιS j₀) ιS hw
  let incl : CommRingCat.of S ⟶ W := CommRingCat.ofHom S.subtype
  have hid : d ≫ incl = 𝟙 W := by
    apply WidePushout.hom_ext
    · intro j
      rw [← Category.assoc, WidePushout.ι_desc]
      ext b <;> rfl
    · rw [← Category.assoc, WidePushout.head_desc, ← WidePushout.arrow_ι (fun _ : J => g) j₀]
      ext a <;> rfl
  have htop : ∀ w : W, w ∈ S := by
    intro w
    have : (d ≫ incl) w = w := by rw [hid]; rfl
    rw [← this]
    exact (d w).2
  refine ⟨⟨hTfin.toFinset, ?_⟩⟩
  rw [Set.Finite.coe_toFinset, Algebra.adjoin_int]
  ext w
  simp only [Algebra.mem_top, iff_true]
  exact htop w

end GlobalTheory

theorem GlobalTheory.cechConerve_obj_finiteType_int : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), Algebra.FiniteType ℤ B →
    ∀ k : SimplexCategory, Algebra.FiniteType ℤ ((Arrow.mk g).cechConerve.obj k) := by
  intro A B g hB k
  exact GlobalTheory.widePushout_finiteType_int (J := Fin (k.len + 1)) A B g hB
