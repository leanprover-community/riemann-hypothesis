module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverBaseChangeOfProperQuasiProjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.VertProj

theorem isProjOver_strHom_zmod : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (l : ℕ) [Fact l.Prime]
    [Algebra (ZMod l) Γ(Z, ⊤)], IsProjOver (strHom (ZMod l) (X := Z)) := by
  intro k _ X p D hX Z i _ l _ _
  have : Module.Finite ℤ k := hX.finite
  have hfin : (Int.castRingHom k).Finite := (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact hfin
  have e : i ≫ p ≫ spMap (Int.castRingHom k) =
      strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l)) := specZIsTerminal.hom_ext _ _
  have : IsProper (strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l))) := by
    rw [← e]; infer_instance
  have hpr : IsProper (strHom (ZMod l) (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))
  have hq : IsQProjOver p := by
    obtain ⟨N, j, hj, hjp⟩ := hX.isProjOver
    exact ⟨N, j, inferInstance, inferInstance, hjp⟩
  have hq₁ := isQProjOver_comp_spMap_of_finiteType hfin.finiteType hq
  have hq₂ := isQProjOver_of_isPullback_spMap (Int.castRingHom (ZMod l))
    (IsPullback.of_hasPullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l)))) hq₁
  let u := Limits.pullback.lift (f := p ≫ spMap (Int.castRingHom k))
    (g := spMap (Int.castRingHom (ZMod l))) i (strHom (ZMod l) Z) e
  have : IsImmersion u := by
    have : IsImmersion (u ≫ Limits.pullback.fst _ _) := by
      rw [Limits.pullback.lift_fst]; infer_instance
    exact IsImmersion.of_comp u (Limits.pullback.fst _ _)
  have hu : u ≫ Limits.pullback.snd _ _ = strHom (ZMod l) Z := Limits.pullback.lift_snd _ _ _
  rw [← hu] at hpr ⊢
  exact isProjOver_of_isProper_of_isImmersion _ hq₂

end GlobalTheory.VertProj
