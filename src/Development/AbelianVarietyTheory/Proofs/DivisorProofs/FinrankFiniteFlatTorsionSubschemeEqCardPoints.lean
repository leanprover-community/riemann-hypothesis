module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionRank

theorem etale_pullback_snd {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (K : Over S) (i : K ⟶ A) (c : ℕ) [Mono i] [IsFinite K.hom]
    [Flat K.hom] (hi : i ^ c = 1) (k : Type) [Field k] (hc : (c : k) ≠ 0) (y : Sp k ⟶ S) :
    Etale (pullback.snd K.hom y) := by
  let A' := (Over.pullback y).obj A
  let K' := (Over.pullback y).obj K
  let i' : K' ⟶ A' := (Over.pullback y).map i
  have hA' : IsAbelianScheme A' := Out.TLinPf.isAb_pullback y A hA
  have := hA'.comm
  have := hA'.smooth
  have hc' : IsUnit (c : Γ(Sp k, ⊤)) := by
    have := (Ne.isUnit hc).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    simpa using this
  have hTe : Etale (torsion A' c).hom := GrpTangent.etale_torsion A' hc'
  have hi' : i' ^ c = 1 := by
    have h := map_pow (Over.pullback y).homMonoidHom i c
    rw [hi, map_one] at h
    exact h.symm
  obtain ⟨j, hj, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion A' c i' hi'
  have : Mono i' := inferInstance
  have hjm : Mono j := mono_of_mono_fac hj
  have hjml : Mono j.left := inferInstanceAs (Mono ((Over.forget _).map j))
  have hju : FormallyUnramified j.left := inferInstance
  have hKu : FormallyUnramified K'.hom := by
    rw [← Over.w j]
    exact MorphismProperty.comp_mem @FormallyUnramified _ _ hju inferInstance
  have : Flat K'.hom := by change Flat (pullback.snd K.hom y); infer_instance
  have : IsFinite K'.hom := by change IsFinite (pullback.snd K.hom y); infer_instance
  have : LocallyOfFinitePresentation K'.hom := inferInstance
  exact Etale.of_formallyUnramified_of_flat K'.hom

theorem finrank_eq_card : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (K : Over S) (i : K ⟶ A) (c : ℕ), Mono i → IsFinite K.hom → Flat K.hom → i ^ c = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (y : Sp k ⟶ S) (z : Sp k), K.hom.finrank (y z) = Nat.card (Over.mk y ⟶ K) := by
  intro S A _ _ hA K i c hi hfin hfl hic k _ _ hc y z
  have het := etale_pullback_snd A hA K i c hic k hc y
  obtain ⟨-, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank (pullback.snd K.hom y) (𝟙 (Sp k)) z
  have hz : (𝟙 (Sp k) : Sp k ⟶ Sp k) z = z := rfl
  rw [hz, Scheme.Hom.finrank_pullback_snd] at hcard
  rw [← hcard]
  refine Nat.card_congr
    { toFun := fun x => Over.homMk (x.1 ≫ pullback.fst K.hom y) (by
        change (x.1 ≫ pullback.fst K.hom y) ≫ K.hom = y
        rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, Category.id_comp])
      invFun := fun g => ⟨pullback.lift g.left (𝟙 _) (by
        rw [Category.id_comp]; exact Over.w g), pullback.lift_snd _ _ _⟩
      left_inv := fun x => Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _)
        ((pullback.lift_snd _ _ _).trans x.2.symm))
      right_inv := fun g => Over.OverMorphism.ext (pullback.lift_fst _ _ _) }

end GlobalTheory.TorsionRank
