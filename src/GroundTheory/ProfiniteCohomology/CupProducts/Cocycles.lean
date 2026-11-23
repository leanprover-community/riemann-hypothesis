module

public import GroundTheory.ProfiniteCohomology.CupProducts
public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
public import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
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

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory groupCohomology

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H] [TopologicalSpace G]
  [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]

instance isDiscreteRep_tensorUnit : IsDiscreteRep (𝟙_ (Rep.{u} k G)) :=
  ⟨fun a => by
    have : stabilizer (𝟙_ (Rep.{u} k G)).ρ a = ⊤ := by
      ext g
      simp [mem_stabilizer]
    rw [this]
    exact isOpen_univ⟩

variable {A : Rep.{u} k G} [IsDiscreteRep A] {p : ℕ}


omit [IsTopologicalGroup H] in
theorem cocycles_ext {x y : cocycles A p}
    (h : cochainOf (A := A) (cocycleι (A := A) (p := p) x) =
      cochainOf (A := A) (cocycleι (A := A) (p := p) y)) : x = y :=
  cocycleι_injective (cochainOf_injective h)


omit [IsTopologicalGroup H] in
@[elab_as_elim]
theorem cohomology_induction_on {C : cohomology A p → Prop} (z : cohomology A p)
    (h : ∀ x : cocycles A p, C (cohomologyπ A p x)) : C z := by
  obtain ⟨x, rfl⟩ := cohomologyπ_surjective A p z
  exact h x

section Map

variable {B : Rep.{u} k G} [IsDiscreteRep B]


omit [IsTopologicalGroup H] in
theorem cochainOf_cocycleι_cyclesMap (f : A ⟶ B) (x : cocycles A p) :
    cochainOf (A := B)
      (cocycleι (A := B) (p := p) (HomologicalComplex.cyclesMap (cochainsMap f) p x)) =
      fun g => f.hom (cochainOf (A := A) (cocycleι (A := A) (p := p) x) g) :=
  congrArg (fun ψ => cochainOf (A := B) (ψ.hom x))
    (HomologicalComplex.cyclesMap_i (cochainsMap f) p)


omit [IsTopologicalGroup H] in
theorem cohomologyMap_cohomologyπ (f : A ⟶ B) (x : cocycles A p) :
    cohomologyMap f p (cohomologyπ A p x) =
      cohomologyπ B p (HomologicalComplex.cyclesMap (cochainsMap f) p x) :=
  ConcreteCategory.congr_hom (cohomologyπ_comp_cohomologyMap f p) x

end Map

section MapAlong

variable {B : Rep.{u} k H} [IsDiscreteRep B] (φ : H →* G) (hφ : Continuous φ)
  (f : Rep.res φ A ⟶ B)

theorem cochainOf_cocycleι_cocyclesMapAlong (x : cocycles A p) :
    cochainOf (A := B) (cocycleι (A := B) (p := p) (cocyclesMapAlong φ hφ f p x)) =
      fun h => f.hom (cochainOf (A := A) (cocycleι (A := A) (p := p) x) (⇑φ ∘ h)) :=
  congrArg (fun ψ => cochainOf (A := B) (ψ.hom x))
    (HomologicalComplex.cyclesMap_i (cochainsMapAlong φ hφ f) p)

theorem cohomologyMapAlong_cohomologyπ (x : cocycles A p) :
    cohomologyMapAlong φ hφ f p (cohomologyπ A p x) =
      cohomologyπ B p (cocyclesMapAlong φ hφ f p x) :=
  ConcreteCategory.congr_hom (cohomologyπ_cohomologyMapAlong φ hφ f p) x

end MapAlong

end GroundTheory.ProfCoh
