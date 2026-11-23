module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVStatement
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.CubeMapTripleProductUnique
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapIdOfCommonGeneric
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSabMapOfGroupIso
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ModelUniqueChecks

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem existsUnique_map (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] (t t' : SAB H (Sp V)) (tK : SAB H (Sp K)) (a : SABMap tK t (spMap (algebraMap V K)))
    (a' : SABMap tK t' (spMap (algebraMap V K))) :
    ∃! ψ : SABMap t t' (𝟙 (Sp V)), a.φ ≫ ψ.φ = a'.φ := by
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap V K)) ∧ IsSchemeTheoreticallyDominant (spMap (algebraMap V K)) :=
    ExtUnique.spec_fractionRing V K
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian t.G t.semi
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian t'.G t'.semi
  obtain ⟨F, hF, hφ⟩ := TripleExt.exists_hom a.cart a'.cart
    (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr V K t.G t'.G t.semi t'.semi)
  obtain ⟨F', -, hφ'⟩ := TripleExt.exists_hom a'.cart a.cart
    (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr V K t'.G t.G t'.semi t.semi)
  have hiso : IsIso F := ExtUnique.isIso_of_isPullback a.cart.1 a'.cart.1 (Iso.refl _) F F'
    ((Category.id_comp _).trans hφ.symm) ((Category.id_comp _).trans hφ'.symm)
  have hact : ∀ x, t.act.act x ≫ F = F ≫ t'.act.act x := fun x =>
    ExtUnique.over_hom_ext_of_isPullback a.cart.1 (by
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← a.act, Category.assoc, hφ, ← Category.assoc, hφ,
        a'.act])
  obtain ⟨n, hn⟩ := GlobalTheory.Exist.CubicalExtension.exists_sabMap_of_groupIso E H V K t t' tK a a'
    (asIso F) hF hφ hact
  refine ⟨n, (congrArg (a.φ ≫ ·) hn).trans hφ, fun n' hn' => SemiAbelianTripleChecks.sabMap_ext _ _ ?_⟩
  have w : n'.φ ≫ t'.G.hom = t.G.hom := n'.cart.1.w.trans (Category.comp_id _)
  have : Over.homMk n'.φ w = F := ExtUnique.over_hom_ext_of_isPullback a.cart.1 (hn'.trans hφ.symm)
  rw [hn]
  exact congrArg (fun z => z.left) this

theorem extV_holds : ExtVStatement := fun _ _ _ _ _ V _ _ _ _ t t' tK _ a a' =>
  (existsUnique_map V (FractionRing V) t t' tK a a').exists

end GlobalTheory.ModelUniqueChecks
