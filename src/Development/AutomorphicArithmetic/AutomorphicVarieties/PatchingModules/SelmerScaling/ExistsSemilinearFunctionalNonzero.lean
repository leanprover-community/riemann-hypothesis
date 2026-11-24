module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurent
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem exists_semilinear_functional_nonzero {O B F M : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Field F] [AddCommGroup M]
    [Module B M] (φ : O →+* B) (f : O →+* F) (hf : Function.Surjective f)
    (hM : ∀ o ∈ maximalIdeal O, ∀ m : M, φ o • m = 0) (q : M) (hq : q ≠ 0) :
    ∃ Φ : M →+ F, (∀ o m, Φ (φ o • m) = f o * Φ m) ∧ Φ q ≠ 0 := by
  letI : Module O M := Module.compHom M φ
  haveI hmax : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  have hker : RingHom.ker f = maximalIdeal O := IsLocalRing.eq_maximalIdeal hmax
  have hT : Module.IsTorsionBySet O M (RingHom.ker f) := by
    rintro m ⟨o, ho⟩
    exact hM o (hker ▸ ho) m
  letI : Field (O ⧸ RingHom.ker f) := Ideal.Quotient.field _
  letI : Module (O ⧸ RingHom.ker f) M := hT.module
  haveI : Module.Free (O ⧸ RingHom.ker f) M := Module.Free.of_divisionRing _ _
  haveI : Module.Projective (O ⧸ RingHom.ker f) M := Module.Projective.of_free
  obtain ⟨Ψ, hΨ⟩ := Module.Projective.exists_dual_ne_zero (O ⧸ RingHom.ker f) hq
  let e := RingHom.quotientKerEquivOfSurjective hf
  refine ⟨(e : (O ⧸ RingHom.ker f) →+* F).toAddMonoidHom.comp Ψ.toAddMonoidHom, fun o m => ?_, ?_⟩
  · show e (Ψ (φ o • m)) = f o * e (Ψ m)
    have hs : (φ o • m : M) = (Ideal.Quotient.mk (RingHom.ker f) o) • m := (hT.mk_smul o m).symm
    rw [hs, map_smul, smul_eq_mul, map_mul, RingHom.quotientKerEquivOfSurjective_apply_mk]
  · show e (Ψ q) ≠ 0
    exact fun h => hΨ (e.injective (h.trans (map_zero e).symm))

theorem UpperTheory.V.Pa.phSep :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ y : S.U.N, (∀ Φ ∈ S.Ph, Φ y = 0) → y ∈ S.J2 • (⊤ : Submodule S.Bh S.U.N) := by
  intro l _ S y hy
  by_contra hne
  let P := S.J2 • (⊤ : Submodule S.Bh S.U.N)
  have hq : (Submodule.Quotient.mk y : S.U.N ⧸ P) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hne
  have hJ : ∀ b ∈ S.J2, ∀ z : S.U.N, b • z ∈ P := fun b hb z => Submodule.smul_mem_smul hb trivial
  have hM : ∀ o ∈ maximalIdeal S.OO, ∀ m : S.U.N ⧸ P, algebraMap S.OO S.Bh o • m = 0 := by
    intro o ho m
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective P m
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hJ _ (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ho))) z
  obtain ⟨Φ0, hΦ0, hne0⟩ :=
    exists_semilinear_functional_nonzero (algebraMap S.OO S.Bh) (S.rF.comp (algebraMap S.OO S.Bh)) S.oo_surj hM _ hq
  let Φ : S.U.N →+ S.F := Φ0.comp P.mkQ.toAddMonoidHom
  have hmem : Φ ∈ S.Ph := by
    refine ⟨fun o z => ?_, fun b hb z => ?_⟩
    · show Φ0 (P.mkQ (algebraMap S.OO S.Bh o • z)) = S.rF (algebraMap S.OO S.Bh o) * Φ0 (P.mkQ z)
      rw [map_smul]
      exact hΦ0 o _
    · show Φ0 (P.mkQ (b • z)) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).mpr (hJ b hb z), map_zero]
  exact hne0 (hy Φ hmem)
