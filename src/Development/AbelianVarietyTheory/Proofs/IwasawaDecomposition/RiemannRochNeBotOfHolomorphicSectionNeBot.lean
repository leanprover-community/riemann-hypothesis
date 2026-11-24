module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

theorem riemannRoch_ne_bot_of_holomorphicSection_ne_bot : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ)
    (R : AnRead Y.str σ Y.dim) (D : Y.Dv), R.holSec (Y.lb D) ≠ ⊥ → Y.H0 D ≠ ⊥ := by
  intro F _ Y σ R D hR hH
  refine hR ?_
  have P := GlobalTheory.Cartier.presents_toLB D
  have hs : ∀ s : (Y.lb D).Sec, s = 0 := fun s => by
    have hm : P.rat s ∈ Y.H0 D := P.rat_mem s
    rw [hH, Submodule.mem_bot] at hm
    exact P.rat_injective (hm.trans (map_zero P.rat).symm)
  have hx : ∀ x : SecC Y.str σ (Y.lb D), x = 0 := fun x => by
    have hle : Submodule.span ℂ (Set.range (SecC.of Y.str σ : (Y.lb D).Sec → _)) ≤ ⊥ :=
      Submodule.span_le.2 (by
        rintro _ ⟨s, rfl⟩
        rw [hs s, map_zero]
        exact zero_mem _)
    exact (Submodule.mem_bot ℂ).1 (hle (SecC.span_range_of.ge Submodule.mem_top))
  have hb := GlobalTheory.AnRead.bijective_valC Y.isProjOver R P.isLB
  refine (Submodule.eq_bot_iff _).2 fun f hf => ?_
  obtain ⟨x, hxf⟩ := hb.2 ⟨f, hf⟩
  rw [hx x, map_zero] at hxf
  exact (congrArg Subtype.val hxf).symm

end GlobalTheory.ShFam.Hor
