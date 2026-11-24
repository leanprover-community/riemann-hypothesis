module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.loc_iff_etale_affine_points : ∀ (U : Scheme.{0})
    (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop),
    (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g)) →
    (_root_.GlobalTheory.EtC.Loc U P ↔ ∀ x : U, ∃ (V : Scheme.{0}) (g : V ⟶ U),
      IsAffine V ∧ Etale g ∧ x ∈ Set.range g ∧ P V g) := by
  intro U P hP
  unfold _root_.GlobalTheory.EtC.Loc
  constructor
  · rintro ⟨S, hS, hSP⟩ x
    obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
    haveI : Scheme.JointlySurjective (Scheme.precoverage (@Etale : MorphismProperty Scheme.{0})) :=
      Scheme.instJointlySurjectivePrecoverage
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    let A := (𝒰.X i).affineCover
    obtain ⟨z, hz⟩ := A.covers y
    have hE : Etale (𝒰.f i) := 𝒰.map_prop i
    refine ⟨A.X (A.idx y), A.f (A.idx y) ≫ 𝒰.f i, inferInstance, inferInstance, ⟨z, ?_⟩, ?_⟩
    · rw [Scheme.Hom.comp_apply, hz]
    · exact hSP _ _ (S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk i)) _)
  · intro h
    choose V g hV hE hx hPg using h
    let S : Sieve U :=
      { arrows := fun W f => P W f, downward_closed := fun hf k => hP _ _ _ k hf }
    refine ⟨S, ?_, fun W f hf => hf⟩
    refine (Scheme.mem_grothendieckTopology_iff (P := @Etale)).2
      ⟨Scheme.Cover.mkOfCovers U V g (fun x => ?_) (fun x => hE x), ?_⟩
    · obtain ⟨y, hy⟩ := hx x
      exact ⟨x, y, hy⟩
    · rintro _ _ ⟨x⟩
      exact hPg x

end GlobalTheory.EtC
