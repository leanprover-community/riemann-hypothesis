module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Generation
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.GlobalGen
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Immersion
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.SerreP
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
  MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjScheme

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {n : ℕ} {X : Scheme.{u}}
  [X.Over (Spec (.of A))] (i : X ⟶ projectiveSpace A n) [IsClosedImmersion i]
  [i.IsOver (Spec (.of A))]


omit [IsNoetherianRing A] [X.Over (Spec (.of A))] [i.IsOver (Spec (.of A))] in
theorem exists_generatingSections_twist (F : X.Modules) (hF : IsCoherent F) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∃ σ : (twist i F q).GeneratingSections, σ.IsFiniteType := by
  have := hF.1
  obtain ⟨q₀, hq₀⟩ := ProjSpace.exists_generatingSections_twist _ (isCoherent_pushforward i hF)
  refine ⟨q₀, fun q hq => ?_⟩
  obtain ⟨σ, hσ⟩ := hq₀ q hq
  exact exists_generatingSections_of_pushforward i (twist i F q)
    (exists_generatingSections_of_iso (pushforwardTwistIso i F q) ⟨σ, hσ⟩)

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

attribute [local instance] algebraOfOver


include i in
theorem finite_H (F : X.Modules) (hF : IsCoherent F) (p : ℕ) :
    Module.Finite A (Sheaf.H.{w'} (modulesAb F) p) := by
  letI := hF.1
  letI := ProjSpace.finite_H.{w'} _ (isCoherent_pushforward i hF) p
  exact Module.Finite.equiv (HLinearEquivPushforward.{w'} i F p).symm

theorem exists_subsingleton_H_twist (F : X.Modules) (hF : IsCoherent F) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ p : ℕ, 0 < p →
      Subsingleton (Sheaf.H.{w'} (modulesAb (twist i F q)) p) := by
  letI := hF.1
  obtain ⟨q₀, hq₀⟩ := ProjSpace.exists_subsingleton_H_twist.{w'} _ (isCoherent_pushforward i hF)
  refine ⟨q₀, fun q hq p hp => ?_⟩
  have h₁ := hq₀ q hq p hp
  have e₁ := HLinearEquivPushforward.{w'} i (twist i F q) p
  have e₂ : Sheaf.H.{w'} (modulesAb (ProjSpace.twist ((Scheme.Modules.pushforward i).obj F) q)) p ≃+
      Sheaf.H.{w'} (modulesAb ((Scheme.Modules.pushforward i).obj (twist i F q))) p :=
    ((H.moduleFunctor.{w'} A p).mapIso (pushforwardTwistIso i F q)).toLinearEquiv.toAddEquiv
  exact e₁.toEquiv.subsingleton_congr.2 (e₂.toEquiv.subsingleton_congr.1 h₁)

end ProjScheme

end

end GroundTheory.Arith.SchemeCoh
