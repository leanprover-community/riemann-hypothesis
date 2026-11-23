module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgHomValuationSubring
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitOfBijectiveMulNatural
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSeriesOfTorsionCharacters
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTateOfCharacter
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
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat

open KernelNoTorsion GmPoints

theorem exists_subgroup_hom_of_tv {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))}
    [GrpObj G] [IsCommMonObj G] {p : ℕ} {R : Type} [CommRing R] [Algebra O R] (ψ : Tv G p) :
    ∃ (H : Subgroup (specO O R ⟶ G)) (θ : H →* Rˣ),
      ∀ (n : ℕ) (w : specO O R ⟶ torsion G (p ^ n)),
        ∃ h : w ≫ torsion.ι G (p ^ n) ∈ H, θ ⟨_, h⟩ = unitOf (w ≫ ψ.χ n) := by
  have hl : ∀ {x : specO O R ⟶ G} {n : ℕ} (m : ℕ), x ^ p ^ n = 1 → x ^ p ^ (n + m) = 1 :=
    fun m hn => by rw [pow_add, pow_mul, hn, one_pow]
  let H : Subgroup (specO O R ⟶ G) :=
    { carrier := {x | ∃ n : ℕ, x ^ p ^ n = 1}
      one_mem' := ⟨0, one_pow _⟩
      mul_mem' := by
        rintro x y ⟨n, hn⟩ ⟨m, hm⟩
        exact ⟨n + m, by rw [mul_pow, hl m hn, add_comm, hl n hm, _root_.one_mul]⟩
      inv_mem' := by
        rintro x ⟨n, hn⟩
        exact ⟨n, by rw [inv_pow, hn, inv_one]⟩ }
  let θ : H → Rˣ := fun x => unitOf (torsionLift x.1 x.2.choose_spec ≫ ψ.χ x.2.choose)
  have hθ : ∀ (x : H) (n : ℕ) (w : specO O R ⟶ torsion G (p ^ n)),
      w ≫ torsion.ι G (p ^ n) = x.1 → θ x = unitOf (w ≫ ψ.χ n) := fun x n w hw =>
    congrArg unitOf (CharGerm.comp_χ_eq ψ _ _ (by rw [hw, torsionLift_ι]))
  refine ⟨H, MonoidHom.mk' θ fun x y => ?_, fun n w =>
    ⟨⟨n, by rw [← MonObj.comp_pow, torsionι_pow, MonObj.comp_one]⟩, hθ _ n w rfl⟩⟩
  obtain ⟨n, hn⟩ := x.2
  obtain ⟨m, hm⟩ := y.2
  have hx : x.1 ^ p ^ (n + m) = 1 := hl m hn
  have hy : y.1 ^ p ^ (n + m) = 1 := by rw [add_comm]; exact hl n hm
  have hxy : (x * y).1 ^ p ^ (n + m) = 1 := by rw [Subgroup.coe_mul, mul_pow, hx, hy, _root_.one_mul]
  rw [hθ x _ _ (torsionLift_ι _ hx), hθ y _ _ (torsionLift_ι _ hy),
    hθ (x * y) _ _ (torsionLift_ι _ hxy), ← unitOf_mul]
  congr 1
  exact ψ.isChar _ _ _ _ _ (by rw [torsionLift_ι, torsionLift_ι, torsionLift_ι]; rfl)

theorem weilChar_surjective_and_map_range_al :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), Function.Surjective P.weilChar ∧ (LinearMap.range P.al).map (omega P.Gt).subtype = htSpan P.Gt p := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  have hs : Function.Surjective P.weilChar := fun χ => by
    obtain ⟨H, θ, hθ⟩ := exists_subgroup_hom_of_tv (R := O) χ
    obtain ⟨κ, hκ⟩ := TorsionCharacter.exists_extend_character (P.toA.comp H.subtype)
      (P.toA_injective.comp H.subtype_injective)
      ((Units.map (algebraMap O C).toMonoidHom).comp θ)
    obtain ⟨s, hs1, hs2⟩ := ChTor.exists_tate_of_character (ChTor.Pts P.A.A) Cˣ p
      (Fact.out : p.Prime).pos (fun a b => mul_comm a b) (weil P.A)
      (fun k hk => ⟨fun l z s hl hz hs => weil_level hk hl hz hs, weil_perfect hk⟩) κ
      fun z z' _ _ => map_mul κ z z'
    refine ⟨Tate.mk s hs1, (P.existsUnique_isWeilChar _).unique (P.isWeilChar_weilChar _)
      fun n w => ?_⟩
    obtain ⟨h, hw⟩ := hθ n w
    rw [Tate.lev_mk, hs2 n _ (P.toA_pow w), ← hw]
    exact (congrArg Units.val (hκ ⟨_, h⟩)).symm
  refine ⟨hs, le_antisymm P.map_range_al_le ?_⟩
  rw [← map_span_dlogTv]
  refine Submodule.map_mono (Submodule.span_le.2 ?_)
  rintro _ ⟨χ, rfl⟩
  obtain ⟨t, rfl⟩ := hs χ
  exact ⟨1 ⊗ₜ t, by rw [P.al_tmul, one_smul]; rfl⟩

end GlobalTheory.HTLat
