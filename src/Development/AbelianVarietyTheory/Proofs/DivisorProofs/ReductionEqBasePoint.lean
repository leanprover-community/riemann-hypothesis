module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.LogKS

open MonObj

theorem IsTranslate.fst_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (x : Sp R ⟶ X) (g₀ : Sp S ⟶ t.G.left) (v : Sp (DualNumber R) ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ x → IsTanAtG t x v → IsTranslate t φ g₀ v w → spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ := by
  intro E _ _ _ H X t R S _ _ φ x g₀ v w hg hv ⟨g', v', h₁, h₂, h₃⟩
  have e1 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1
  have e2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ) =
      spMap φ ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun a => by simp [dualMap]
  let r : Over.mk (g₀ ≫ t.G.hom) ⟶ tEpsG (g₀ ≫ t.G.hom) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      show _ ≫ spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom = g₀ ≫ t.G.hom
      rw [← Category.assoc, e1, Category.id_comp])
  let q : Over.mk (g₀ ≫ t.G.hom) ⟶ Over.mk x := Over.homMk (spMap φ) hg.symm
  have hv1 : r ≫ v' = 1 := by
    rw [← MonObj.comp_one q]
    apply Over.OverMorphism.ext
    show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v'.left = spMap φ ≫ _
    rw [h₂, ← Category.assoc, e2, Category.assoc, hv.2]
  have h : (r ≫ (g' * v')).left = (r ≫ g').left := by
    rw [MonObj.comp_mul, hv1, _root_.mul_one]
  rw [← h₃]
  refine h.trans ?_
  show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ g'.left = g₀
  rw [h₁, ← Category.assoc, e1, Category.id_comp]

end GlobalTheory.LogKS
