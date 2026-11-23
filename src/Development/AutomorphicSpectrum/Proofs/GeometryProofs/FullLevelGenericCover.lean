module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelStructurePropertiesStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelStructurePullbackStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem unitAt_of_pow_eq_one {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (hN : Flat.NormalCpt ξ)
    {N : ℕ} (hN0 : N ≠ 0) {a : Ω} (ha : a ^ N = 1) (q : Cpt ξ) : unitAt ξ q a :=
  Flat.ZUnit.of_pow_of_normal hN hN0 (by rw [ha]; exact Flat.ZUnit.one)

theorem exists_full_level_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (K Ω : Type) [Field K] [Field Ω] [CharZero Ω] (i : K →+* Ω) (y : Sp K ⟶ Xo.XF c) (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk (spMap i ≫ y ≫ Y.j) ⟶ Y.t.G)), 1 ≤ N → IsFullLevelAt D Y.t (spMap i ≫ y ≫ Y.j) N z ev → ∀ (X : Scheme.{0}) (ξ : Sp Ω ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ f : X ⟶ Y.X, ξ ≫ f = spMap i ≫ y ≫ Y.j → ∃ (t : SAB H X) (_ : SABMap t Y.t f) (ev' : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev' ∧ FullTorsion t.G ξ N ∧ ∀ q : Cpt ξ, unitAt ξ q (z : Ω) := by
  intro E _ _ _ H D l Xo c Y K Ω _ _ _ i y N z ev hN hlev X ξ _ hnorm f hf
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull f Y.t
  have hid : ξ ≫ f = spMap (RingHom.id Ω) ≫ spMap i ≫ y ≫ Y.j := by
    rw [hf]
    have : spMap (RingHom.id Ω) = 𝟙 _ := by simp [spMap]
    rw [this, Category.id_comp]
  obtain ⟨ev', hev', -⟩ := GlobalTheory.T.full_level_structure_pullback E H D Y.X X Y.t t f m Ω Ω (RingHom.id Ω) (spMap i ≫ y ≫ Y.j) ξ hid N z ev hlev
  have hz : Units.map (RingHom.id Ω).toMonoidHom z = z := by ext; rfl
  rw [hz] at hev'
  obtain ⟨hprim, -, -, -, -, hfull, -⟩ := GlobalTheory.T.full_level_structure_properties E H D X t Ω ξ N hN z ev' hev'
  refine ⟨t, m, ev', hev', hfull, fun q => ?_⟩
  have hpow : (z : Ω) ^ N = 1 := by
    have := congrArg Units.val hprim.pow_eq_one
    simpa using this
  exact unitAt_of_pow_eq_one hnorm (by omega) hpow q

end GlobalTheory.CompanionTheory.Ar.XR
