module

public import Development.EtaleCohomology.TateTwists.EtaleLocalIffAffineEtaleCoverPointwise
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_sheaf_section_locally_iff_of_presheaf_facts : EtaleLocalIffAffineEtaleCoverPointwise := by
  intro U P hP
  constructor
  · rintro ⟨S, hS, hSP⟩ x
    obtain ⟨𝒰, hle⟩ := (Scheme.mem_grothendieckTopology_iff (P := (@Etale : MorphismProperty Scheme.{0}))).mp hS
    obtain ⟨i, y, hy⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).mp 𝒰.mem₀).1 x
    let 𝒱 := (𝒰.X i).affineCover
    obtain ⟨z, hz⟩ := 𝒱.covers y
    refine ⟨𝒱.X (𝒱.idx y), 𝒱.f (𝒱.idx y) ≫ 𝒰.f i, inferInstance, ?_, ⟨z, ?_⟩, ?_⟩
    · have : Etale (𝒰.f i) := 𝒰.map_prop i
      infer_instance
    · simp only [Scheme.Hom.comp_apply, hz, hy]
    · exact hSP _ _ (S.downward_closed (hle _ _ (Presieve.ofArrows.mk i)) _)
  · intro h
    choose V g hA hE hx hPg using h
    refine ⟨{ arrows := fun W k => P W k, downward_closed := fun {Y Z f} hf k => hP Y Z f k hf }, ?_, ?_⟩
    · refine (Scheme.mem_grothendieckTopology_iff (P := (@Etale : MorphismProperty Scheme.{0}))).mpr ⟨Scheme.Cover.mkOfCovers (P := (@Etale : MorphismProperty Scheme.{0})) U V g (fun x => ⟨x, hx x⟩) (fun x => hE x), ?_⟩
      rintro W k ⟨x⟩
      exact hPg x
    · intro W k hk
      exact hk

end LateralTheory.EtaleFoundations
