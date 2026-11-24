module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPositiveDefiniteQuadraticFormEndomorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleCubicalLineBundleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisibleAlgClosureOfKillsTorsionSepClosedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfActsTriviallyAbelianVarietyAlgClosureStatement
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdCoordsOfDefiniteParallelogramForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateModuleLevelComponentEqOfCardTorsion
public import Mathlib.NumberTheory.Padics.RingHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntExistsLevelNotDvdMulLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdEndomorphismPowLevelComponentEqOneOfRelationStatement
import Mathlib
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.ExistsLinearIndependentNormLe

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CMFaithful

theorem linearIndependent_actTate : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → (∃ d : ℕ, 0 < d ∧ SmoothOfRelativeDimension d A.hom) → ∀ (F : Type) [Field F] [NumberField F] (O : Type) [CommRing O] [Algebra O F] [IsFractionRing O F] (α : OAct O A) (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (n : ℕ) (a : Fin n → O), LinearIndependent ℚ (fun i => algebraMap O F (a i)) → LinearIndependent ℤ_[l] (fun i => actTate α.toRingAct l (ptOver K Ω) (a i)) := by
  intro K Ω _ _ _ _ A _ _ hA hd F _ _ O _ _ _ α l _ hl n a ha
  obtain ⟨d, hd0, hdim⟩ := hd
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  let t := spMap (algebraMap K (AlgebraicClosure Ω))
  let B := (Over.pullback t).obj A
  let β := OAct.pullback t A α
  have hB : IsAbelianScheme B := GlobalTheory.isAbelianScheme_pullback_obj t A hA
  haveI : IsCommMonObj B := hB.comm
  obtain ⟨L, hL⟩ := GlobalTheory.T.exists_symmetric_ample_cubical_lineBundle_abelianVariety (AlgebraicClosure Ω) B hB
  obtain ⟨Q, hQ1, hQ2, hQ3, -⟩ := GlobalTheory.SS.exists_quadraticForm_end (AlgebraicClosure Ω) B hB L hL
  let ψ : O →+ Additive (B ⟶ B) := AddMonoidHom.mk' (fun x => Additive.ofMul (β.act x))
    (fun x y => by rw [β.add]; rfl)
  let H : AddSubgroup (Additive (B ⟶ B)) :=
    { carrier := {f | IsMonHom (Additive.toMul f)}
      add_mem' := fun {f g} hf hg => by
        change IsMonHom (Additive.toMul f * Additive.toMul g)
        haveI : IsMonHom (Additive.toMul f) := hf
        haveI : IsMonHom (Additive.toMul g) := hg
        rw [Hom.mul_def]; infer_instance
      zero_mem' := by
        change IsMonHom (1 : B ⟶ B)
        rw [Hom.one_def]; infer_instance
      neg_mem' := fun {f} hf => by
        change IsMonHom (Additive.toMul f)⁻¹
        haveI : IsMonHom (Additive.toMul f) := hf
        infer_instance }
  have hu : ∀ i, ψ (a i) ∈ H := fun i => β.hom (a i)
  have hinj : Function.Injective ψ := (injective_iff_map_eq_zero ψ).2 fun x hx =>
    GlobalTheory.T.eq_zero_of_acts_trivially_abelianVariety_algClosure K Ω A hA ⟨d, hd0, hdim⟩ l hl F O α x (by
      have : Additive.toMul (ψ x) = Additive.toMul 0 := congrArg _ hx
      exact this)
  have hindep : LinearIndependent ℤ (fun i => ψ (a i)) := by
    have h1 : LinearIndependent ℤ (fun i => algebraMap O F (a i)) := ha.restrict_scalars' ℤ
    have h2 : LinearIndependent ℤ a := by
      refine LinearIndependent.of_comp (algebraMap O F).toAddMonoidHom.toIntLinearMap ?_
      exact h1
    exact h2.map' ψ.toIntLinearMap (LinearMap.ker_eq_bot.2 hinj)
  obtain ⟨e, he, hE⟩ := _root_.GlobalTheory.exists_dvd_coords_of_definite_form (Additive (B ⟶ B)) H (fun f => Q (Additive.toMul f))
    (fun f g => by
      have := hQ1 (Additive.toMul f) (Additive.toMul g)
      exact this)
    (fun f => hQ2 _) (fun f hf h0 => by
      have := hQ3 (Additive.toMul f) hf h0
      exact this) n (fun i => ψ (a i)) hu hindep
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push_neg at hne
  obtain ⟨j, hj⟩ := hne
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.padicInt_toZModPow_not_dvd_mul l (c j) hj e he
  haveI : NeZero (l ^ N) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let m : Fin n → ℤ := fun i => ((PadicInt.toZModPow N (c i)).val : ℤ)
  have hm : ∀ i, PadicInt.toZModPow N (c i) = (m i : ZMod (l ^ N)) := fun i => by
    simp [m]
  let φ : Fin n → ((ptOver K Ω ⟶ A) →* (ptOver K Ω ⟶ A)) := fun i => actPts α.toRingAct (ptOver K Ω) (a i)
  have kill := _root_.GlobalTheory.TateRel.prod_pow_eq_one (ptOver K Ω ⟶ A) l n φ c hc N m hm
  let x : O := ∑ i, m i • a i
  have hcomp : ∀ y : ptOver K Ω ⟶ A, y ≫ α.act x = ∏ i, (y ≫ α.act (a i)) ^ m i := by
    intro y
    let χ : O →+ Additive (ptOver K Ω ⟶ A) := AddMonoidHom.mk' (fun z => Additive.ofMul (y ≫ α.act z))
      (fun z w => by rw [α.add, MonObj.comp_mul]; rfl)
    have e1 : χ x = ∑ i, m i • χ (a i) := by simp only [x, map_sum, map_zsmul]
    have e2 := congrArg Additive.toMul e1
    rw [toMul_sum] at e2
    simp only [toMul_zsmul] at e2
    exact e2
  have hcard : ∀ k : ℕ, Nat.card {y : ptOver K Ω ⟶ A // y ^ (l ^ k) = 1} = l ^ (2 * d * k) := fun k => by
    rw [GlobalTheory.T.card_abelianVariety_torsion_sepClosed K Ω A hA d hdim (l ^ k) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl), ← pow_mul, mul_comm k]
  have hx : ∀ y : ptOver K Ω ⟶ A, y ^ (l ^ N) = 1 → y ≫ α.act x = 1 := by
    intro y hy
    obtain ⟨tt, rfl⟩ := _root_.GlobalTheory.exists_tate_lev_eq_of_card_torsion (ptOver K Ω ⟶ A) l (2 * d) hcard N y hy
    rw [hcomp, ← kill tt]
    rfl
  obtain ⟨h, hh, hfh⟩ := GlobalTheory.T.divisible_algClosure_of_kills_torsion_sepClosed K Ω A hA (l ^ N) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl) (α.act x) (α.hom x) hx
  have hsum : (l ^ N) • Additive.ofMul h = ∑ i, m i • ψ (a i) := by
    rw [← ofMul_pow, ← hfh]
    change ψ x = _

    simp only [x, map_sum, map_zsmul]
  have := hE (l ^ N) m (Additive.ofMul h) hh hsum j
  exact hN (m j) (hm j) (by exact_mod_cast this)

end GlobalTheory.CMFaithful
