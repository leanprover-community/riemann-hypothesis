module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImageCocycleSemilinearSheafComplexMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedUnit

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map φ y) = Sec.map φ (Sec.res g y) := by
  have := congrArg (fun f => f.hom y) (φ.hom.naturality g.op)
  exact this.symm

theorem res_resGen {q : ℕ} [NeZero q] (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (ζ.map g.appTop.hom) := by
  unfold resGen
  rw [res_map, (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 V U g ζ]

theorem val_one_smul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (y : M) :
    (1 : ZMod q).val • y = y := by
  by_cases hq : q = 1
  · subst hq
    have : Subsingleton M := Module.subsingleton (ULift.{1} (ZMod 1)) M
    exact Subsingleton.elim _ _
  · haveI : Fact (1 < q) := ⟨by have := NeZero.ne q; omega⟩
    rw [ZMod.val_one, one_smul]

theorem resGen_zero_eq {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) : resGen 0 ζ = resGen 0 ξ := by
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).1
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.1 ζ ξ
  refine ⟨S, hS, fun W h hh => ?_⟩
  obtain ⟨a, ha⟩ := hP W h hh
  rw [res_resGen, res_resGen]
  have := (GlobalTheory.T.tateTwist_sections_locally_generated q 0).2.2.2.2.1 W (ζ.map h.appTop.hom) (ξ.map h.appTop.hom) a ha
  unfold resGen
  rw [this, zpow_zero, Units.val_one, val_one_smul]

end GlobalTheory.EtC.RedUnit

theorem GlobalTheory.EtC.red_one : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → red Q q E 0 0 (one Q E) = one q E := by
  intro Q q _ hqQ E hE
  haveI : NeZero q := ⟨fun h => by subst h; exact NeZero.ne Q (Nat.eq_zero_of_zero_dvd hqQ)⟩
  have hEq : Inv q E := fun U hU => by
    obtain ⟨k, hk⟩ := hqQ
    have := hE U hU
    rw [hk, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨α, hα1, hα2⟩ := (GlobalTheory.T.tateTwistUnitClass_rootClass_spec Q).1 E hE
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 0)).1 E 0 α
  have hred : red Q q E 0 0 (one Q E) = CohomologyClass.mk β := by
    rw [← hα1]; exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 0)).2 E 0 α β hβ
  rw [hred]
  refine (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.1 E hEq β fun U x ξ => ?_
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).1
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).1 (hE U ⟨x⟩)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hP V g hg
  obtain ⟨ξ', hξ'⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(V, ⊤)).2.2.2.2.2 q hqQ ζ
  rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β.1 0 0 _ V U g x, hβ 0 0 _ V (x.res g), hα2 V (x.res g) ζ,
    GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ 0 V ζ ξ' hξ', RedUnit.res_resGen]
  exact RedUnit.resGen_zero_eq _ _
