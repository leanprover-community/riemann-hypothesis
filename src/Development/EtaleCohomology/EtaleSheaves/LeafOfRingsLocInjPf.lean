module

public import Development.EtaleCohomology.EtaleSheaves.LeafTwSecKillCut
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec

theorem jointlySurj_prec (P : MorphismProperty Scheme.{0}) : Scheme.JointlySurjective (Scheme.precoverage P) :=
  inferInstance

theorem LeafOfRingsLocInj_of : LeafOfRingsLocInj := by
  intro R _ M U t ht u
  have h0 : (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U) t =
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U) 0 := by
    have : ofRings.sec M U t = 0 := ht
    simp only [ofRings.sec] at this
    rw [map_zero]
    exact this
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) t 0 h0
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  have := jointlySurj_prec @Etale
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq u
  refine ⟨𝒰.X i, 𝒰.f i, 𝒰.map_prop i, ⟨y, hy⟩, ?_⟩
  have hm := hle _ _ (Presieve.ofArrows.mk i)
  have hm' : ((Scheme.Γ ⋙ M).map (𝒰.f i).op).hom t = ((Scheme.Γ ⋙ M).map (𝒰.f i).op).hom 0 := hm
  rw [map_zero] at hm'
  exact hm'

end LateralTheory.E.E8.TwSec
