module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Ideal.Maps
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
public import Mathlib.RingTheory.Ideal.Quotient.Defs

@[expose] public section

open CategoryTheory Limits

namespace GlobalTheory.TorsionChart

theorem pushout_inl_surjective_and_ker {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ D} {j : C ⟶ D} (po : IsPushout f g i j) (hg : Function.Surjective g.hom) :
    Function.Surjective i.hom ∧ RingHom.ker i.hom = Ideal.map f.hom (RingHom.ker g.hom) := by
  set I := Ideal.map f.hom (RingHom.ker g.hom) with hIdef
  have hw : ∀ a, i.hom (f.hom a) = j.hom (g.hom a) := fun a => congr($(po.w).hom a)
  have hI : I ≤ RingHom.ker i.hom := by
    rw [hIdef, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, hw, (RingHom.mem_ker).1 ha, map_zero]
  let mk : B ⟶ CommRingCat.of (B ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have hker : RingHom.ker g.hom ≤ RingHom.ker ((Ideal.Quotient.mk I).comp f.hom) := by
    intro a ha
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  let φ : {g' : A →+* B ⧸ I // RingHom.ker g.hom ≤ RingHom.ker g'} :=
    ⟨(Ideal.Quotient.mk I).comp f.hom, hker⟩
  let ψ : C ⟶ CommRingCat.of (B ⧸ I) := CommRingCat.ofHom (g.hom.liftOfSurjective hg φ)
  have hψ : f ≫ mk = g ≫ ψ := by
    ext a
    exact (RingHom.liftOfSurjective_comp_apply g.hom hg φ a).symm
  let lift : CommRingCat.of (B ⧸ I) ⟶ D := CommRingCat.ofHom (Ideal.Quotient.lift I i.hom hI)
  have h1 : i ≫ po.desc mk ψ hψ = mk := po.inl_desc _ _ _
  have h2 : po.desc mk ψ hψ ≫ lift = 𝟙 D := by
    refine po.hom_ext ?_ ?_
    · rw [← Category.assoc, h1, Category.comp_id]
      ext b
      rfl
    · rw [← Category.assoc, po.inr_desc, Category.comp_id]
      ext c
      obtain ⟨a, rfl⟩ := hg c
      change lift.hom (ψ.hom (g.hom a)) = j.hom (g.hom a)
      rw [show ψ.hom (g.hom a) = mk.hom (f.hom a) from
        (RingHom.liftOfSurjective_comp_apply g.hom hg φ a), ← hw]
      rfl
  refine ⟨fun d => ?_, le_antisymm (fun b hb => ?_) hI⟩
  · obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((po.desc mk ψ hψ).hom d)
    refine ⟨b, ?_⟩
    have := congr($(h2).hom d)
    change lift.hom ((po.desc mk ψ hψ).hom d) = d at this
    rw [← hb] at this
    exact this
  · have := congr($(h1).hom b)
    change (po.desc mk ψ hψ).hom (i.hom b) = Ideal.Quotient.mk I b at this
    rw [(RingHom.mem_ker).1 hb, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm

end GlobalTheory.TorsionChart
