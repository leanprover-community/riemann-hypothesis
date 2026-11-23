module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSymmetricIffExistsGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.ZH

theorem exists_cp_zhOut : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE, ∃ P : GlobalTheory.UU.CP Z.G, P.L = Z.L := by
  intro o Ω _ _ _ _ S ρS M U₀ EE hO Z
  obtain ⟨s, hs, hr⟩ := GlobalTheory.SymmetricBundle.gen_of_isSymmetric Z.L Z.sym

  have hrange : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hO.ne (Set.mem_univ w)
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hrange
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _

  have w' : pullback.fst Z.G.hom M.pt ≫ Z.G.hom = (((Over.pullback M.pt).obj Z.G).hom ≫ x) ≫ U₀.ι := by
    rw [Category.assoc, hx]; exact pullback.condition
  let φ' := Z.cart.1.lift (pullback.fst Z.G.hom M.pt) (((Over.pullback M.pt).obj Z.G).hom ≫ x) w'
  have n : IsGrpPullback ((Over.pullback M.pt).obj Z.G) Z.G (x ≫ U₀.ι) (φ' ≫ Z.φ) :=
    (isGrpPullback_pullback Z.G M.pt).congr hx.symm (Z.cart.1.lift_fst _ _ _).symm
  have h1 := IsGrpPullback.cancel Z.cart n (Z.cart.1.lift_snd _ _ _)
  have h2 := (IsGrpPullback.comp h1 (isGrpPullback_pullback ρS.P.A Z.u₀)).congr (Z.u₀_gen x hx) rfl
  have hA : IsAbelianScheme ((Over.pullback M.pt).obj Z.G) :=
    GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback ρS.P.isAb h2
  have h3 := GlobalTheory.ValueForm.surjective_cube_baseChange GlobalTheory.globalFns_holds M.pt hA (Iso.refl _)

  have := Z.semi.smooth
  have : Flat (G3 Z.G).hom := by
    show Flat (pullback.fst Z.G.hom (pullback.fst Z.G.hom Z.G.hom ≫ Z.G.hom) ≫ Z.G.hom)
    infer_instance
  have := M.sep
  have : QuasiCompact M.pt := by infer_instance
  have : IsSchemeTheoreticallyDominant M.pt := IsSchemeTheoreticallyDominant.of_isDominant M.pt
  have : IsSchemeTheoreticallyDominant (pullback.fst (G3 Z.G).hom M.pt) :=
    .of_isPullback (IsPullback.of_hasPullback (G3 Z.G).hom M.pt).flip
  have hi : ∀ U, Function.Injective ((pullback.fst (G3 Z.G).hom M.pt).app U).hom :=
    fun U => (pullback.fst (G3 Z.G).hom M.pt).app_injective U
  exact ⟨⟨Z.L, Z.cub, s, hs, hr, GlobalTheory.ValueForm.sym_cub_of_baseChange M.pt hi h3 Z.cub s hs hr⟩, rfl⟩

end GlobalTheory.ZH
