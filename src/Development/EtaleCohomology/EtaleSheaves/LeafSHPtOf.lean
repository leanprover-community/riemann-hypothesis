module

public import Development.EtaleCohomology.EtaleSheaves.LeafSHPtPf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StrictHenselianPoint
open LateralTheory.E.E4 LateralTheory.E.LeafDegCut LateralTheory.E.LeafSHPtPf

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
theorem leafSHTop : LeafSHTop := by
  intro B U x J _ _ D c V a e t ht hcof
  obtain ⟨j0⟩ := (inferInstance : Nonempty J)
  constructor
  · intro O hxO
    have hU : Etale U.hom := U.prop
    let U' : B.Etale := MorphismProperty.Over.mk ⊤ (O.ι ≫ U.hom) (by
      change Etale (O.ι ≫ U.hom); infer_instance)
    let b : U' ⟶ U := MorphismProperty.Over.homMk (A := U') (B := U) O.ι rfl
    obtain ⟨j, g, hg⟩ := hcof U' b ⟨x, hxO⟩ rfl
    rintro _ ⟨z, rfl⟩
    rw [← ht j, ← hg]
    have : Set.range (O.ι) ⊆ (O : Set U.left) := by rw [Scheme.Opens.range_ι]
    apply this
    exact ⟨(Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ g) z, by
      rfl⟩
  · intro S hS
    obtain ⟨𝒰, _, h, hU⟩ := (Scheme.mem_smallGrothendieckTopology _ _).1 hS
    obtain ⟨i, ⟨u, hu⟩⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).1 𝒰.mem₀).1 x
    let fi : (𝒰.X i).asOverProp B (h i) ⟶ U := (𝒰.f i).asOverProp B
    refine ⟨_, fi, hU _ _ ⟨i⟩, ?_⟩
    obtain ⟨j, g, hg⟩ := hcof _ fi u hu
    exact ⟨Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ g, by
      rw [Category.assoc, Category.assoc, hg, ht j]⟩

theorem LeafSHPt_of (hN : LateralTheory.E.LeafSHPtPf.LeafSHNb) : LateralTheory.E.LeafInj0VPf.LeafSHPt :=
  LateralTheory.E.LeafSHPtPf.LeafSHPt_of hN leafSHTop

end LateralTheory.E.StrictHenselianPoint
