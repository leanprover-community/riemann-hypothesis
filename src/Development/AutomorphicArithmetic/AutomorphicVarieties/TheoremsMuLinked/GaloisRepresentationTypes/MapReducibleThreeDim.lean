module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GRepresents
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeD
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem norm_lt_one_of_nonunit {l : ℕ} [Fact l.Prime] (c : Coef l) (b : c.O) (hb : ¬ IsUnit b) :
    ‖(b : PadicAlgCl l)‖ < 1 := by
  haveI := c.dvr
  haveI := c.fin
  by_cases h0 : b = 0
  · subst h0
    simp
  have hv0 : IsDiscreteValuationRing.addVal c.O b ≠ 0 := fun h =>
    hb (IsDiscreteValuationRing.addVal_eq_zero_iff.mp h)
  have hvt : IsDiscreteValuationRing.addVal c.O b ≠ ⊤ := fun h =>
    h0 (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
  have hk : (IsDiscreteValuationRing.addVal c.O b).toNat ≠ 0 := by
    intro h
    rw [ENat.toNat_eq_zero] at h
    tauto
  have key := normO l c.O b h0
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr : ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal c.O b).toNat < 1 :=
    pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl) hk
  by_contra hge
  push_neg at hge
  have h1 := one_le_pow₀ (n := (eO l c.O).toNat) hge
  linarith

private theorem isLocPt_toBar {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R]
    [IsCO c.O R] (x : R →ₐ[c.O] c.O) : IsLocPt (toBar x) := by
  intro y hy
  have hsurj : Function.Surjective x := fun a => ⟨algebraMap c.O R a, x.commutes a⟩
  have hmax : (Ideal.comap (x : R →+* c.O) (IsLocalRing.maximalIdeal c.O)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ hsurj
  have heq := IsLocalRing.eq_maximalIdeal hmax
  have hy' : y ∈ Ideal.comap (x : R →+* c.O) (IsLocalRing.maximalIdeal c.O) := heq ▸ hy
  have hxy : x y ∈ IsLocalRing.maximalIdeal c.O := hy'
  exact norm_lt_one_of_nonunit c (x y) ((IsLocalRing.mem_maximalIdeal _).mp hxy)

private theorem map_reducible_three_dim {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (η : G →* ℤˣ)
    (Ψ : G →* Rˣ) : (GG.map f).comp (r0 η Ψ) = r0 η ((Units.map f.toMonoidHom).comp Ψ) := by
  ext g : 1
  apply SemidirectProduct.ext
  · apply Units.ext
    ext i j
    simp only [MonoidHom.comp_apply, GG.map, r0, MonoidHom.coe_mk, OneHom.coe_mk,
      SemidirectProduct.map_left, GeneralLinearGroup.map_apply, tor_val, RingHom.mapMatrix_apply]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.map_apply, Matrix.diagonal_apply_eq]
      exact congrArg Units.val (map_zpow (Units.map (f : R →* S)) (Ψ g) (wt1 i))
    · simp [Matrix.diagonal_apply_ne _ hij]
  · simp [GG.map, r0]

private theorem coboundary_of_mem_B1 {Γ κ : Type} [Group Γ] [CommRing κ] (r : Γ →* GG (m := 3) (R := κ))
    (γ : Γ → Matrix (Fin 3) (Fin 3) κ) (h : γ ∈ ReciprocityTheory.Gal.B1 (adRep r)) : ∃ X, γ = cob r X := by
  obtain ⟨X, hX⟩ := LinearMap.mem_range.mp h
  refine ⟨-X, ?_⟩
  funext g
  rw [← hX]
  show adRep r g X - X = -X - adRep r g (-X)
  rw [map_neg]
  abel

private theorem isPush_push {O Γ R κ : Type} [CommRing O] [Group Γ] [CommRing R] [Algebra O R] [CommRing κ]
    [Algebra O κ] (f : R →ₐ[O] κ) (r : Γ →* GG (m := 3) (R := R)) : IsPush (f.comp (entAlg O r).val) r (push f r) := by
  intro g
  refine ⟨rfl, fun a b => ⟨?_, rfl⟩⟩
  unfold entAlg
  exact Algebra.subset_adjoin ⟨g, a, b, rfl⟩
