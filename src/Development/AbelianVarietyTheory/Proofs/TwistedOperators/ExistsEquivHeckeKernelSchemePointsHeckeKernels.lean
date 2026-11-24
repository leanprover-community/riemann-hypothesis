module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeKernelSchemeGeometricPointsEqKernels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.FibrePushforward
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

theorem exists_carried (Z : KerScheme Xo P p i) {k : Type} [Field k] [IsAlgClosed k] (w : Sp k ⟶ Z.Hk)
    (y : Sp k ⟶ Xo.X) (hw : w ≫ Z.π₁ = y) :
    ∃ C : Subgroup (Over.mk y ⟶ Xo.univ.t.G), Xo.univ.t.HeckeKer (Over.mk y) Dw P p i C ∧
      ∀ C', Z.Carries w y C' ↔ C' = C := by
  subst hw
  obtain ⟨C₀, hC₀, hk⟩ := Z.hecke k w
  obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv Z.m₁.cart (Over.mk w)
  have hh : ∀ (u : Over.mk w ⟶ Z.o₁.t.G) (v : Over.mk (w ≫ Z.π₁) ⟶ Xo.univ.t.G),
      v.left = u.left ≫ Z.m₁.toSABMap.φ → (u ∈ C₀ ↔ v ∈ Subgroup.comap ρ.symm.toMonoidHom C₀) := fun u v e => by
    rw [show v = ρ u from Over.OverMorphism.ext (e.trans (e₀ u).symm)]
    show _ ↔ ρ.symm (ρ u) ∈ C₀
    rw [ρ.symm_apply_apply]
  refine ⟨Subgroup.comap ρ.symm.toMonoidHom C₀,
    (GlobalTheory.HkSetPull.heckeKer_iff Dw P p i Z.m₁.toSABMap (Over.mk w) C₀ _ hh).1 hk, fun C' => ⟨fun h => ?_, ?_⟩⟩
  · ext v
    obtain ⟨u, rfl⟩ := ρ.surjective v
    exact (h.2 u _ (e₀ u)).symm.trans ((hC₀ u).symm.trans (hh u _ (e₀ u)))
  · rintro rfl
    exact ⟨rfl, fun u v e => (hC₀ u).symm.trans (hh u v e)⟩

theorem exists_equiv_carries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo P p i), admitted l P p → ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X), ∃ e : {w : Sp k ⟶ Z.Hk // w ≫ Z.π₁ = y} ≃ {C : Subgroup (Over.mk y ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk y) Dw P p i C}, ∀ w C, Z.Carries w.1 y C ↔ C = (e w).1 := by
  intro E _ _ _ H Dw l Xo P p i Z hA k _ _ y
  choose c hc hcc using fun w : {w : Sp k ⟶ Z.Hk // w ≫ Z.π₁ = y} => exists_carried Z w.1 y w.2
  refine ⟨Equiv.ofBijective (fun w => ⟨c w, hc w⟩) ⟨fun w w' e => ?_, fun C => ?_⟩, hcc⟩
  · exact Subtype.ext (((GlobalTheory.kerScheme_points E H Dw l Xo P p i Z hA).1 k y (c w) (hc w)).unique
      ((hcc w _).2 rfl) ((hcc w' _).2 (congrArg Subtype.val e)))
  · obtain ⟨z, hz, -⟩ := (GlobalTheory.kerScheme_points E H Dw l Xo P p i Z hA).1 k y C.1 C.2
    exact ⟨⟨z, hz.1⟩, Subtype.ext ((hcc ⟨z, hz.1⟩ _).1 hz).symm⟩

end GlobalTheory.HeckeEx
