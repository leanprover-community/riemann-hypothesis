module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.IsDualPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PhiSub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem fin_step {A : Type} [AddCommGroup A] (l : ℕ) (h1 : {a : A | l • a = 0}.Finite) (j : ℕ) :
    {a : A | l ^ j • a = 0}.Finite := by
  induction j with
  | zero =>
    apply Set.Finite.subset (Set.finite_singleton 0)
    intro a ha
    simp only [Set.mem_setOf_eq, pow_zero, one_smul] at ha
    simp [ha]
  | succ j ih =>
    have hsub : {a : A | l ^ (j + 1) • a = 0} ⊆ (fun a => l • a) ⁻¹' {a : A | l ^ j • a = 0} := by
      intro a ha
      simp only [Set.mem_setOf_eq, Set.mem_preimage] at ha ⊢
      rw [smul_smul, ← pow_succ]; exact ha
    refine Set.Finite.subset (Set.Finite.preimage' ih ?_) hsub
    intro b _
    by_cases hne : ((fun a : A => l • a) ⁻¹' {b}).Nonempty
    · obtain ⟨a0, ha0⟩ := hne
      refine Set.Finite.subset (h1.image (fun x => x + a0)) ?_
      intro a ha
      refine ⟨a - a0, ?_, by simp⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha ha0
      simp only [Set.mem_setOf_eq, smul_sub, ha, ha0, sub_self]
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]; exact Set.finite_empty

theorem UpperTheory.V.Th.finZK :
    ∀ (l : ℕ) [Fact l.Prime] (k : ℕ) (R Γ M : Type) [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M), PhiCond Γ l → LC ρ → (∀ m : M, l ^ k • m = 0) → Finite (Zl ρ) := by
  intro l _ k R Γ M _ _ _ _ _ _ _ _ ρ hphi hlc htors
  classical
  let M1 : Submodule R M :=
    { carrier := {m | l • m = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun r {m} hm => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_comm, hm, smul_zero] }
  have hst : ∀ g, ∀ m ∈ M1, ρ g m ∈ M1 := by
    intro g m hm
    show l • ρ g m = 0
    rw [← map_nsmul, show l • m = 0 from hm, map_zero]
  let ρ1 : Representation R Γ M1 :=
    { toFun := fun g => (ρ g).restrict (hst g)
      map_one' := by
        refine LinearMap.ext fun m => Subtype.ext ?_
        simp
      map_mul' := fun g h => by
        refine LinearMap.ext fun m => Subtype.ext ?_
        simp }
  have hlc1 : LC ρ1 := fun m => IsLocallyConstant.desc _ Subtype.val (hlc m.1) Subtype.val_injective
  have htors1 : ∀ m : M1, l • m = 0 := by
    intro m
    have h : l • (m : M) = 0 := m.2
    apply Subtype.ext
    simpa using h
  have hfin1 : Finite (Zl ρ1) := (finZ l R Γ M1 ρ1 hphi hlc1 htors1).1
  have hl : {a : Zl ρ | l • a = 0}.Finite := by
    have hval : ∀ a : {a : Zl ρ // l • a = 0}, ∀ g, (a.1 : Γ → M) g ∈ M1 := by
      intro a g
      have h := congrArg (fun x : Zl ρ => (x : Γ → M) g) a.2
      show l • (a.1 : Γ → M) g = 0
      simpa using h
    have hmemF : ∀ a : {a : Zl ρ // l • a = 0},
        (fun g => (⟨(a.1 : Γ → M) g, hval a g⟩ : M1)) ∈ Zl ρ1 := by
      intro a
      obtain ⟨hlc', hcoc⟩ := (mem_Zl ρ).mp a.1.2
      exact (mem_Zl ρ1).mpr ⟨IsLocallyConstant.desc _ Subtype.val hlc' Subtype.val_injective,
        fun g h => Subtype.ext (hcoc g h)⟩
    let F : {a : Zl ρ // l • a = 0} → Zl ρ1 := fun a => ⟨_, hmemF a⟩
    have hF : Function.Injective F := by
      intro a b hab
      apply Subtype.ext; apply Subtype.ext; funext g
      have := congrFun (congrArg Subtype.val hab) g
      exact congrArg Subtype.val this
    haveI : Finite ↥{a : Zl ρ | l • a = 0} := Finite.of_injective F hF
    exact Set.toFinite _
  have hk := fin_step l hl k
  have huniv : {a : Zl ρ | l ^ k • a = 0} = Set.univ := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    apply Subtype.ext
    funext g
    simp [htors]
  rw [huniv] at hk
  exact Set.finite_univ_iff.mp hk
