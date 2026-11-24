module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtOfGeometricPoints
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFactor

lemma ext_of_geometricPoints {T X Z : Scheme.{0}} [IsReduced T] (q : X ⟶ Z) [IsSeparated q]
    (f g : T ⟶ X) (h : f ≫ q = g ≫ q)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), x ≫ f = x ≫ g) : f = g := by
  apply (config := { allowSynthFailures := true }) GlobalTheory.HkFam.hom_ext_of_geometric_points <;> assumption

theorem exists_unique_factor : ∀ (S : Scheme.{0}) [IsReduced S] (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B'] (ψ : A ⟶ B) (g : A ⟶ B'), IsAbelianScheme A → IsAbelianScheme B → IsSeparated B'.hom → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → IsMonHom g → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A), x ≫ ψ = 1 → x ≫ g = 1) → ∃ g' : B ⟶ B', IsMonHom g' ∧ ψ ≫ g' = g ∧ ∀ g'' : B ⟶ B', ψ ≫ g'' = g → g'' = g' := by
  intro S _ A B B' _ _ _ ψ g _ _ hsep hψ hfin het hsurj hg H

  let T : Over S := pullback ψ η[B]
  let i : T ⟶ A := pullback.fst ψ η[B]
  have hker : IsPullback i (toUnit T) ψ η[B] := by
    have hp := IsPullback.of_hasPullback ψ η[B]
    rwa [toUnit_unique (pullback.snd ψ η[B]) (toUnit T)] at hp

  have : IsReduced T.left := by
    have hp : IsPullback i.left (toUnit T).left ψ.left (η[B]).left := hker.map (Over.forget S)
    have : Etale (toUnit T).left := MorphismProperty.of_isPullback hp het
    have : IsReduced (𝟙_ (Over S)).left := by dsimp; infer_instance
    exact GlobalTheory.isReduced_of_smooth_of_isReduced (toUnit T).left
  have := hsep

  have hf : i ≫ g = toUnit T ≫ η[B'] := by
    apply Over.OverMorphism.ext
    refine ext_of_geometricPoints B'.hom _ _ (by rw [Over.w, Over.w]) ?_
    intro k _ _ x
    let xo : Over.mk (x ≫ T.hom) ⟶ T := Over.homMk x
    have e1 : (xo ≫ i) ≫ ψ = 1 := by
      rw [Category.assoc, hker.w, ← Category.assoc, Hom.one_def, toUnit_unique (xo ≫ toUnit T) (toUnit _)]
    have e3 : xo ≫ (i ≫ g) = xo ≫ (toUnit T ≫ η[B']) := by
      rw [← Category.assoc, H k (x ≫ T.hom) (xo ≫ i) e1, Hom.one_def, ← Category.assoc,
        toUnit_unique (xo ≫ toUnit T) (toUnit _)]
    simpa only [xo, Over.comp_left, Over.homMk_left] using congrArg CommaMorphism.left e3
  have := hψ; have := hg; have := hfin; have := het; have := hsurj
  obtain ⟨β, hβ, hψβ⟩ := FlatQuotient.exists_desc ψ i g hker hf
  have : Epi ψ := FlatQuotient.epi_of_flat_surjective ψ
  exact ⟨β, hβ, hψβ, fun g'' h'' => (cancel_epi ψ).1 (h''.trans hψβ.symm)⟩

end GlobalTheory.HkFactor
