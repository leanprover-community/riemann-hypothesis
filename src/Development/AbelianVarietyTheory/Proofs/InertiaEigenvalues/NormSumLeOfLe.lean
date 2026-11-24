module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValCCuspOfSmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneTmulMemSupLatticeOfMemLocalUnitBall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCuspFormsFullLattice
public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormEqOfMemClosure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCp
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGoodOfBddAll
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidue
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmulMemSupLattice
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
import Mathlib.RingTheory.PiTensorProduct
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsSat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOneOfMemLocalUnitBallSide, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisRationalFormsLocalUnitBall, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteUnramifiedApproximationPadic, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserNormGapPadicEmbedding, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisTer, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupLatticeRationalFormMemLocalUnitBall, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitBallFiniteUnramifiedDescentComplexPadic, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsFurther, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightVectorRealizationExists, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSumLeOfLe

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOneOfMemLocalUnitBallSide =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOneOfMemLocalUnitBallSide", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValCCuspOfSmul\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneTmulMemSupLatticeOfMemLocalUnitBall\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

set_option autoImplicit false
noncomputable section



namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nrm_le_one_of_mem_locBall_pts : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f ∈ locBall YS fw iC b j, ∀ y : (Rl.FW j).Pt (placeC YS iC b), (Rl.FW j).nrm (placeC YS iC b) y ⟨(YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1, ((YS.fi j).wk _).1 (show ↥(S.A ((j : ℕ) + 1)).WK from f).2⟩ ≤ 1 := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j f hf y
  have h := nrm_le_one_of_mem_locBall YS fw iC b j hf y
  have he : fw.e j (cuspOf YS fw j f) = ⟨(YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1,
      ((YS.fi j).wk _).1 (show ↥(S.A ((j : ℕ) + 1)).WK from f).2⟩ :=
    Subtype.ext (e_cuspOf YS fw j f)
  rw [he] at h
  exact h

end GlobalTheory.GeoTie
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOneOfMemLocalUnitBallSide =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisRationalFormsLocalUnitBall =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisRationalFormsLocalUnitBall", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValCCuspOfSmul\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCuspFormsFullLattice\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOneOfMemLocalUnitBallSide\nimport Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmulMemSupLattice\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

set_option autoImplicit false
noncomputable section


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocBasis

theorem exists_basis_of_loc (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
    (V : Type) [AddCommGroup V] [Module K V] (N : Set V)
    (h0 : (0 : V) ∈ N) (hadd : ∀ f ∈ N, ∀ g ∈ N, f + g ∈ N)
    (hsm : ∀ (x t : 𝓞 K), t ∉ P.asIdeal → ∀ f ∈ N, ((x : K) / (t : K)) • f ∈ N)
    (hsp : ∀ f : V, ∃ c : K, c ≠ 0 ∧ c • f ∈ N)
    (m : ℕ) (g : Fin m → V)
    (hbd : ∀ f ∈ N, ∃ t : 𝓞 K, t ∉ P.asIdeal ∧ ∃ c : Fin m → 𝓞 K, (t : K) • f = ∑ k, (c k : K) • g k) :
    ∃ (n : ℕ) (B : Module.Basis (Fin n) K V), (∀ s, B s ∈ N) ∧
      ∀ f ∈ N, ∀ s, ∃ x t : 𝓞 K, t ∉ P.asIdeal ∧ B.repr f s = (x : K) / (t : K) := by
  classical
  have hle : P.asIdeal.primeCompl ≤ nonZeroDivisors (𝓞 K) := fun t ht =>
    mem_nonZeroDivisors_of_ne_zero fun h => ht (h ▸ P.asIdeal.zero_mem)
  let R := Localization.subalgebra.ofField K P.asIdeal.primeCompl hle
  haveI : IsLocalization.AtPrime R P.asIdeal := (inferInstance : IsLocalization P.asIdeal.primeCompl R)
  haveI : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) P.ne_bot R
  have mk'_coe : ∀ (x : 𝓞 K) (t : P.asIdeal.primeCompl),
      ((IsLocalization.mk' R x t : R) : K) = (x : K) / ((t : 𝓞 K) : K) := by
    intro x t
    have ht : ((t : 𝓞 K) : K) ≠ 0 := by
      intro h
      exact t.2 ((show (t : 𝓞 K) = 0 by exact_mod_cast h) ▸ P.asIdeal.zero_mem)
    rw [eq_div_iff ht]
    have h := congrArg (algebraMap R K) (IsLocalization.mk'_spec R x t)
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    exact h
  have memR : ∀ r : R, ∃ x t : 𝓞 K, t ∉ P.asIdeal ∧ (r : K) = (x : K) / (t : K) := by
    intro r
    obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.asIdeal.primeCompl r
    exact ⟨x, t, t.2, mk'_coe x t⟩
  have inR : ∀ x t : 𝓞 K, t ∉ P.asIdeal → ∃ r : R, (r : K) = (x : K) / (t : K) :=
    fun x t ht => ⟨IsLocalization.mk' R x (⟨t, ht⟩ : P.asIdeal.primeCompl), mk'_coe x ⟨t, ht⟩⟩
  have smul_def : ∀ (r : R) (f : V), r • f = (r : K) • f := fun r f => rfl
  let NR : Submodule R V :=
    { carrier := N
      add_mem' := fun {a b} ha hb => hadd a ha b hb
      zero_mem' := h0
      smul_mem' := fun r f hf => by
        obtain ⟨x, t, ht, hr⟩ := memR r
        change r • f ∈ N
        rw [smul_def, hr]
        exact hsm x t ht f hf }
  let L : Submodule R V := Submodule.span R (Set.range g)
  have hNL : NR ≤ L := by
    intro f hf
    obtain ⟨t, ht, c, hc⟩ := hbd f hf
    have ht0 : (t : K) ≠ 0 := by
      intro h
      exact ht ((show t = 0 by exact_mod_cast h) ▸ P.asIdeal.zero_mem)
    have hf' : f = ∑ k, ((c k : K) / (t : K)) • g k := by
      have : f = (t : K)⁻¹ • ((t : K) • f) := by rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
      rw [this, hc, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, div_eq_inv_mul]
    rw [hf']
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨r, hr⟩ := inR (c k) t ht
    rw [← hr, ← smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  haveI : Module.Finite R L := Module.Finite.span_of_finite R (Set.finite_range g)
  haveI : NoZeroSMulDivisors R V := ⟨fun {r f} h => by
    rw [smul_def] at h
    rcases smul_eq_zero.1 h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h⟩
  haveI : NoZeroSMulDivisors R L := ⟨fun {r x} h =>
    (smul_eq_zero.1 (congrArg Subtype.val h : r • (x : V) = 0)).imp id fun h' => Subtype.ext h'⟩
  haveI : Module.IsTorsionFree R L := inferInstance
  haveI : Module.Free R L := Module.free_of_finite_type_torsion_free'
  obtain ⟨n, B'⟩ := Submodule.basisOfPidOfLE hNL (Module.Free.chooseBasis R L)
  let v : Fin n → V := fun s => ((B' s : NR) : V)
  have hliR : LinearIndependent R v :=
    B'.linearIndependent.map' NR.subtype (Submodule.ker_subtype NR)
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing R K).1 hliR
  have hexp : ∀ y : NR, (y : V) = ∑ s, ((B'.repr y s : R) : K) • v s := by
    intro y
    have h := congrArg (fun y : NR => (y : V)) (B'.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← h]
    rfl
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    intro f _
    obtain ⟨c, hc, hcf⟩ := hsp f
    have h1 : c • f ∈ Submodule.span K (Set.range v) := by
      rw [show c • f = ((⟨c • f, hcf⟩ : NR) : V) from rfl, hexp]
      exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
    have h2 := Submodule.smul_mem _ c⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
  let B := Module.Basis.mk hli hspan
  have hBv : ∀ s, B s = v s := fun s => Module.Basis.mk_apply hli hspan s
  refine ⟨n, B, fun s => ?_, fun f hf s => ?_⟩
  · rw [hBv]; exact (B' s).2
  · have e1 : f = B.equivFun.symm (fun s => ((B'.repr ⟨f, hf⟩ s : R) : K)) := by
      rw [Module.Basis.equivFun_symm_apply]
      simp only [hBv]
      exact hexp ⟨f, hf⟩
    have e2 : B.repr f s = ((B'.repr ⟨f, hf⟩ s : R) : K) := by
      have e3 := congrArg (fun u => B.equivFun u s) e1
      simp only [LinearEquiv.apply_symm_apply] at e3
      rw [← Module.Basis.equivFun_apply]
      exact e3
    obtain ⟨x, t, ht, hr⟩ := memR (B'.repr ⟨f, hf⟩ s)
    exact ⟨x, t, ht, e2.trans hr⟩

end GlobalTheory.LocBasis

namespace GlobalTheory.GeoTie

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw}
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem supLattice_fg (YS : NX.NExpRealS Rl cG S) (fw : FWTie T0 Rl.toRealDat κ v₀) (j : Fin D.R.m) : ((S.A ((j : ℕ) + 1)).MK).FG := by
  classical
  obtain ⟨m, g', hg'⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (GlobalTheory.GoodLat.Obj.mkFull_of_tie fw j).1
  have hsc : ∀ (a : S.Ks) (w : Fin (Rl.nW j) → D.what₂.LL),
      (YS.fi j).e.symm ((YS.fi j).eK a • w) = a • (YS.fi j).e.symm w := by
    intro a w
    rw [← algebraMap_smul D.what₂.LL ((YS.fi j).eK a) w, (YS.fi j).eK_LL, LinearEquiv.map_smul, algebraMap_smul]
  let d : 𝓞 T0.Q.c.F → 𝓞 S.Ks := fun c =>
    ⟨(YS.fi j).eK.symm (c : T0.Q.c.F), map_isIntegral_int (YS.fi j).eK.symm.toRingHom c.isIntegral_coe⟩
  refine Submodule.fg_iff_exists_fin_generating_family.2 ⟨m, fun k => (YS.fi j).e.symm (g' k), le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine ((YS.fi j).mkK _).2 ?_
    rw [LinearEquiv.apply_symm_apply, ← hg']
    exact Submodule.subset_span ⟨k, rfl⟩
  · intro x hx
    have h1 : (YS.fi j).e x ∈ Submodule.span (𝓞 T0.Q.c.F) (Set.range g') := by
      rw [hg']; exact ((YS.fi j).mkK x).1 hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun k => d (c k), ?_⟩
    calc ∑ k, d (c k) • (YS.fi j).e.symm (g' k) = (YS.fi j).e.symm (∑ k, c k • g' k) := by

          rw [map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← algebraMap_smul T0.Q.c.F (c k) (g' k)]
          have e1 : ((c k : T0.Q.c.F)) = (YS.fi j).eK ((YS.fi j).eK.symm (c k)) := ((YS.fi j).eK.apply_symm_apply _).symm
          rw [show algebraMap (𝓞 T0.Q.c.F) T0.Q.c.F (c k) = (c k : T0.Q.c.F) from rfl, e1, hsc,
            ← algebraMap_smul S.Ks (d (c k))]
          rfl
      _ = x := by rw [hc, LinearEquiv.symm_apply_apply]

end GlobalTheory.GeoTie

namespace GlobalTheory.GeoTie

theorem locBall_basis_exists : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) → ∃ (n : ℕ) (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))), (∀ s, B s ∈ locBall YS fw iC b j) ∧ ∀ g ∈ locBall YS fw iC b j, ∀ s, ‖embS S iC b (B.repr g s)‖ ≤ 1 := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC hiC b j hsp
  classical
  set P := placeAt (embS S iC b) with hP
  have hS1 : ∀ f ∈ locBall YS fw iC b j, ∃ t : 𝓞 S.Ks, t ∉ P.asIdeal ∧
      (show ↥(S.A ((j : ℕ) + 1)).WK from ((t : S.Ks) • f : NX.FmK S ((j : ℕ) + 1))).1 ∈ (S.A ((j : ℕ) + 1)).MK := by
    have hS1a : ∀ f ∈ locBall YS fw iC b j, ∀ y : (Rl.FW j).Pt (placeC YS iC b),
        (Rl.FW j).nrm (placeC YS iC b) y ⟨(YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1,
          ((YS.fi j).wk _).1 (show ↥(S.A ((j : ℕ) + 1)).WK from f).2⟩ ≤ 1 :=
      _root_.GlobalTheory.GeoTie.nrm_le_one_of_mem_locBall_pts D Γ Pl0 I0 T1 A3 T0 Rl cG S YS κ v₀ fw i iC hiC b j
    intro f hf
    obtain ⟨s, hs, hsf⟩ := _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice _ _ _ _ _ (Rl.FW j)
      (GlobalTheory.GoodLat.Obj.mkFull_of_tie fw j).2 (placeC YS iC b) _ (hS1a f hf)
    have heK : ∀ a : S.Ks, (YS.fi j).eK a = eKs YS a := fun a =>
      (algebraMap T0.Q.c.F D.what₂.LL).injective (((YS.fi j).eK_LL a).trans (eKs_LL YS a).symm)
    let t : 𝓞 S.Ks := ⟨(YS.fi j).eK.symm (s : T0.Q.c.F), map_isIntegral_int (YS.fi j).eK.symm.toRingHom s.isIntegral_coe⟩
    have ht : eKs YS (t : S.Ks) = (s : T0.Q.c.F) := by
      rw [← heK]; exact (YS.fi j).eK.apply_symm_apply _
    refine ⟨t, ?_, ?_⟩
    · intro htP
      apply hs
      change ‖embC YS iC b (s : T0.Q.c.F)‖ < 1
      rw [← ht, embC_eKs]
      exact htP
    · refine ((YS.fi j).mkK _).2 ?_
      change (YS.fi j).e ((t : S.Ks) • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1) ∈ (Rl.FW j).MK
      rw [← algebraMap_smul D.what₂.LL (t : S.Ks), LinearEquiv.map_smul, ← (YS.fi j).eK_LL, algebraMap_smul, heK, ht]
      rw [← algebraMap_smul T0.Q.c.F s] at hsf
      exact hsf
  have hS2 : ((S.A ((j : ℕ) + 1)).MK).FG := supLattice_fg YS fw j

  have hunit : ∀ t : 𝓞 S.Ks, t ∉ P.asIdeal → ‖embS S iC b (t : S.Ks)‖ = 1 := fun t ht =>
    le_antisymm (norm_int_le_one _ t) (not_lt.1 ht)
  have hloc : ∀ x t : 𝓞 S.Ks, t ∉ P.asIdeal → ‖embS S iC b ((x : S.Ks) / (t : S.Ks))‖ ≤ 1 := by
    intro x t ht
    rw [map_div₀, norm_div, hunit t ht, div_one]
    exact norm_int_le_one _ x

  have h0 : (0 : NX.FmK S ((j : ℕ) + 1)) ∈ locBall YS fw iC b j := by
    intro z
    rw [map_zero]
    simp [valC_zero]
  have hadd : ∀ f ∈ locBall YS fw iC b j, ∀ g ∈ locBall YS fw iC b j, f + g ∈ locBall YS fw iC b j := by
    intro f hf g hg z
    rw [map_add (f := _), Submodule.coe_add, valC_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf z) (hg z))
  have hsm : ∀ (x t : 𝓞 S.Ks), t ∉ P.asIdeal → ∀ f ∈ locBall YS fw iC b j,
      (((x : S.Ks) / (t : S.Ks)) • f) ∈ locBall YS fw iC b j := by
    intro x t ht f hf z
    rw [valC_cuspOf_smul, norm_mul]
    exact mul_le_one₀ (hloc x t ht) (norm_nonneg _) (hf z)
  obtain ⟨m, g0, hg0⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hS2
  have hgWK : ∀ k, g0 k ∈ (S.A ((j : ℕ) + 1)).WK := fun k => by
    have h : g0 k ∈ (S.A ((j : ℕ) + 1)).MK := hg0 ▸ Submodule.subset_span ⟨k, rfl⟩
    exact h.1
  let g : Fin m → NX.FmK S ((j : ℕ) + 1) := fun k => ⟨g0 k, hgWK k⟩
  have hbd : ∀ f ∈ locBall YS fw iC b j, ∃ t : 𝓞 S.Ks, t ∉ P.asIdeal ∧ ∃ c : Fin m → 𝓞 S.Ks,
      (t : S.Ks) • f = ∑ k, (c k : S.Ks) • g k := by
    intro f hf
    obtain ⟨t, ht, htf⟩ := hS1 f hf
    rw [← hg0] at htf
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 htf
    refine ⟨t, ht, c, Subtype.ext ?_⟩
    rw [← hc]
    change _ = (S.A ((j : ℕ) + 1)).WK.subtype (∑ k, (c k : S.Ks) • g k)
    refine Eq.trans ?_ (map_sum (S.A ((j : ℕ) + 1)).WK.subtype
      (fun k => ((c k : S.Ks) • g k : ↥(S.A ((j : ℕ) + 1)).WK)) Finset.univ).symm
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (algebraMap_smul S.Ks (c k) (g0 k)).symm
  obtain ⟨n, B, hB, hrep⟩ := GlobalTheory.LocBasis.exists_basis_of_loc S.Ks P (NX.FmK S ((j : ℕ) + 1))
    (locBall YS fw iC b j) h0 hadd hsm hsp m g hbd
  refine ⟨n, B, hB, fun f hf s => ?_⟩
  obtain ⟨x, t, ht, hx⟩ := hrep f hf s
  rw [hx]
  exact hloc x t ht

end GlobalTheory.GeoTie
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisRationalFormsLocalUnitBall =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteUnramifiedApproximationPadic =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteUnramifiedApproximationPadic", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormEqOfMemClosure\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KurApprox
open Polynomial
variable {p : ℕ} [Fact p.Prime]

section Val

variable {K : Type} [Field K] [NumberField K] (ψ : K →+* ℂ_[p])

theorem valuation_eq_exp {x : K} (hx : x ≠ 0) :
    (placeAt ψ).valuation K x = WithZero.exp (-vLa (placeAt ψ) x) := by
  rw [vLa, neg_neg, WithZero.exp_log (((placeAt ψ).valuation K).ne_zero_iff.2 hx)]

theorem exists_uniformizer : ∃ π : K, π ≠ 0 ∧ vLa (placeAt ψ) π = 1 ∧ ‖ψ π‖ < 1 := by
  set P := placeAt ψ
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  have hπ1 : P.intValuation π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hπn : ‖ψ (π : K)‖ < 1 := (mem_placeAt ψ π).1 ((P.intValuation_lt_one_iff_mem π).1 hπ1)
  have hνπ : P.valuation K (π : K) = WithZero.exp (-1) := by
    rw [← hπ]; exact HeightOneSpectrum.valuation_of_algebraMap P π
  have hπ0 : (π : K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hνπ
    exact WithZero.exp_ne_zero hνπ.symm
  refine ⟨π, hπ0, ?_, hπn⟩
  simp [vLa, P, hνπ]

theorem norm_eq_zpow {π : K} (hπ0 : π ≠ 0) (hπ : vLa (placeAt ψ) π = 1) {x : K} (hx : x ≠ 0) :
    ‖ψ x‖ = ‖ψ π‖ ^ vLa (placeAt ψ) x := by
  set P := placeAt ψ
  set n := vLa P x
  set b := x * π ^ (-n) with hb
  have hb0 : b ≠ 0 := mul_ne_zero hx (zpow_ne_zero _ hπ0)
  have hνb : P.valuation K b = 1 := by
    rw [hb, map_mul, map_zpow₀, valuation_eq_exp ψ hx, valuation_eq_exp ψ hπ0, hπ, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg, n]
    rw [show -vLa (placeAt ψ) x + vLa P x = 0 from neg_add_cancel _, WithZero.exp_zero]
  have h1 : ‖ψ b‖ ≤ 1 := GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one ψ hνb.le
  have h2 : ‖ψ b⁻¹‖ ≤ 1 := GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one ψ (by rw [map_inv₀, hνb, inv_one])
  have hpos : 0 < ‖ψ b‖ := norm_pos_iff.2 ((map_ne_zero ψ).2 hb0)
  have hb1 : ‖ψ b‖ = 1 := by
    rw [map_inv₀, norm_inv] at h2
    exact le_antisymm h1 ((inv_le_one₀ hpos).1 h2)
  have hxb : x = b * π ^ n := by
    rw [hb, mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]
  rw [hxb, map_mul, norm_mul, hb1, one_mul, map_zpow₀, norm_zpow]

end Val

section Unram

variable {F F' : Type} [Field F] [NumberField F] [Field F'] [NumberField F'] [Algebra F F']

theorem vLa_eq_of_mem_kurC (φ : F →+* ℂ_[p]) (φ' : F' →+* ℂ_[p]) (hcomp : ∀ a, φ' (algebraMap F F' a) = φ a)
    (hk : ∀ x, φ' x ∈ kurC φ) (a : F) : vLa (placeAt φ') (algebraMap F F' a) = vLa (placeAt φ) a := by
  by_cases ha : a = 0
  · subst ha; simp [vLa]
  obtain ⟨π, hπ0, hπ, hπn⟩ := exists_uniformizer φ
  obtain ⟨π', hπ0', hπ', hπn'⟩ := exists_uniformizer φ'
  set c := ‖φ π‖ with hc
  set c' := ‖φ' π'‖ with hc'
  have hc0 : 0 < c := norm_pos_iff.2 ((map_ne_zero φ).2 hπ0)
  have hc0' : 0 < c' := norm_pos_iff.2 ((map_ne_zero φ').2 hπ0')
  obtain ⟨b, hb⟩ := GlobalTheory.KurValue.exists_norm_eq φ (hk π')
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, norm_zero] at hb
    exact hc0'.ne' hb
  have e1 : c' = c ^ vLa (placeAt φ) b := by rw [hc', hb, norm_eq_zpow φ hπ0 hπ hb0]
  have hι0 : algebraMap F F' π ≠ 0 := (_root_.map_ne_zero _).2 hπ0
  have e2 : c = c' ^ vLa (placeAt φ') (algebraMap F F' π) := by
    rw [hc, ← hcomp, norm_eq_zpow φ' hπ0' hπ' hι0]
  have hinj := zpow_right_injective₀ hc0 hπn.ne
  have hmk : vLa (placeAt φ) b * vLa (placeAt φ') (algebraMap F F' π) = 1 := by
    apply hinj
    change c ^ (_ * _) = c ^ (1 : ℤ)
    rw [zpow_mul, ← e1, ← e2, zpow_one]
  have hm : vLa (placeAt φ) b = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hmk with h | h
    · exact h.1
    · exfalso
      rw [h.1, zpow_neg_one] at e1
      have : 1 < c⁻¹ := (one_lt_inv₀ hc0).2 hπn
      linarith
  rw [hm, zpow_one] at e1
  have hιa : algebraMap F F' a ≠ 0 := (_root_.map_ne_zero _).2 ha
  have e3 := norm_eq_zpow φ' hπ0' hπ' hιa
  rw [hcomp, norm_eq_zpow φ hπ0 hπ ha, ← hc, ← hc', e1] at e3
  exact (hinj e3).symm

end Unram

section Approx

variable {F : Type} [Field F] (φ : F →+* ℂ_[p])

def adjRoots (N : ℕ) : IntermediateField F (PAt φ) :=
  IntermediateField.adjoin F {x : PAt φ | x ^ N = 1}

theorem finite_roots {N : ℕ} (hN : 0 < N) : {x : PAt φ | x ^ N = 1}.Finite := by
  classical
  refine ((nthRoots N (1 : PAt φ)).toFinset.finite_toSet).subset fun x hx => ?_
  simpa [Polynomial.mem_nthRoots hN] using hx

theorem finiteDimensional_adjRoots {N : ℕ} (hN : 0 < N) : FiniteDimensional F (adjRoots φ N) := by
  haveI := (finite_roots φ hN).to_subtype
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  have h : x ^ N = 1 := hx
  exact IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one)

theorem numberField_adjRoots [NumberField F] {N : ℕ} (hN : 0 < N) : NumberField (adjRoots φ N) := by
  haveI := finiteDimensional_adjRoots φ hN
  haveI : FiniteDimensional ℚ (adjRoots φ N) := Module.Finite.trans F (adjRoots φ N)
  constructor

theorem adjRoots_mono {N M : ℕ} (h : N ∣ M) : adjRoots φ N ≤ adjRoots φ M := by
  obtain ⟨k, rfl⟩ := h
  refine IntermediateField.adjoin.mono _ _ _ fun x hx => ?_
  have hx' : x ^ N = 1 := hx
  show x ^ (N * k) = 1
  rw [pow_mul, hx', one_pow]

theorem adjRoots_le_kurC {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (z : PAt φ) (hz : z ∈ adjRoots φ N) :
    toCp φ z ∈ kurC φ := by
  let Kt : IntermediateField F (PAt φ) :=
    (show Subfield (PAt φ) from kurC φ).toIntermediateField fun a => mem_kurC φ a
  have hle : adjRoots φ N ≤ Kt := by
    refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
    have hx' : x ^ N = 1 := hx
    exact root_mem_kurC (p := p) φ hpN hx'
  exact hle hz

def kurAlg : Subfield ℂ_[p] where
  carrier := {z | ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ (show PAt φ from z) ∈ adjRoots φ N}
  mul_mem' := by
    rintro x y ⟨N, hN, hpN, hx⟩ ⟨M, hM, hpM, hy⟩
    refine ⟨N * M, Nat.mul_pos hN hM, fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h with h | h
      exacts [hpN h, hpM h]
    · exact mul_mem (adjRoots_mono φ (dvd_mul_right N M) hx) (adjRoots_mono φ (dvd_mul_left M N) hy)
  one_mem' := ⟨1, one_pos, (Fact.out : p.Prime).not_dvd_one, one_mem _⟩
  add_mem' := by
    rintro x y ⟨N, hN, hpN, hx⟩ ⟨M, hM, hpM, hy⟩
    refine ⟨N * M, Nat.mul_pos hN hM, fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h with h | h
      exacts [hpN h, hpM h]
    · exact add_mem (adjRoots_mono φ (dvd_mul_right N M) hx) (adjRoots_mono φ (dvd_mul_left M N) hy)
  zero_mem' := ⟨1, one_pos, (Fact.out : p.Prime).not_dvd_one, zero_mem _⟩
  neg_mem' := by
    rintro x ⟨N, hN, hpN, hx⟩
    exact ⟨N, hN, hpN, neg_mem hx⟩
  inv_mem' := by
    rintro x ⟨N, hN, hpN, hx⟩
    exact ⟨N, hN, hpN, inv_mem hx⟩

theorem kurC_le : kurC φ ≤ (kurAlg φ).topologicalClosure := by
  refine Subfield.topologicalClosure_minimal _ (sup_le ?_ ?_) (Subfield.isClosed_topologicalClosure _)
  · rintro _ ⟨a, rfl⟩
    exact Subfield.le_topologicalClosure _ ⟨1, one_pos, (Fact.out : p.Prime).not_dvd_one,
      IntermediateField.algebraMap_mem _ a⟩
  · refine Subfield.topologicalClosure_minimal _ ?_ (Subfield.isClosed_topologicalClosure _)
    refine (Subfield.closure_le.2 ?_).trans (Subfield.le_topologicalClosure _)
    rintro ζ ⟨n, hn, hpn, hζ⟩
    exact ⟨n, hn, hpn, IntermediateField.subset_adjoin _ _ hζ⟩

end Approx

end GlobalTheory.KurApprox

namespace GlobalTheory.KurApprox

theorem kur_approx : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (n : ℕ)
    (y : Fin n → ℂ_[p]), (∀ s, y s ∈ kurC φ) → ∀ ε : ℝ, 0 < ε →
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (_ : Algebra F F') (φ' : F' →+* ℂ_[p]),
      (∀ a, φ' (algebraMap F F' a) = φ a) ∧ (∀ a : F, vLa (placeAt φ') (algebraMap F F' a) = vLa (placeAt φ) a) ∧
      ∃ a' : Fin n → F', ∀ s, ‖y s - φ' (a' s)‖ < ε := by
  intro p _ F _ _ φ n y hy ε hε
  have h1 : ∀ s, ∃ z : ℂ_[p], ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ (show PAt φ from z) ∈ adjRoots φ N ∧ ‖y s - z‖ < ε := by
    intro s
    have hs : y s ∈ closure ((kurAlg φ : Subfield ℂ_[p]) : Set ℂ_[p]) := kurC_le φ (hy s)
    obtain ⟨z, ⟨N, hN, hpN, hz⟩, hd⟩ := Metric.mem_closure_iff.1 hs ε hε
    exact ⟨z, N, hN, hpN, hz, by rwa [dist_eq_norm] at hd⟩
  choose z N hN hpN hz hd using h1
  set M := ∏ s, N s with hM
  have hM0 : 0 < M := Finset.prod_pos fun s _ => hN s
  have hpM : ¬ p ∣ M := by
    intro h
    obtain ⟨s, _, hs⟩ := ((Fact.out : p.Prime).prime.dvd_finsetProd_iff _).1 h
    exact hpN s hs
  let K := adjRoots φ M
  haveI : NumberField K := numberField_adjRoots φ hM0
  let φ' : K →+* ℂ_[p] := (toCp φ).comp (algebraMap K (PAt φ))
  have hcomp : ∀ a, φ' (algebraMap F K a) = φ a := fun a => rfl
  have hk : ∀ x : K, φ' x ∈ kurC φ := fun x => adjRoots_le_kurC φ hM0 hpM x x.2
  have hzM : ∀ s, (show PAt φ from z s) ∈ K := fun s =>
    adjRoots_mono φ (Finset.dvd_prod_of_mem N (Finset.mem_univ s)) (hz s)
  exact ⟨K, inferInstance, inferInstance, inferInstance, φ', hcomp, vLa_eq_of_mem_kurC φ φ' hcomp hk,
    fun s => ⟨z s, hzM s⟩, fun s => hd s⟩

end GlobalTheory.KurApprox
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteUnramifiedApproximationPadic =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserNormGapPadicEmbedding =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserNormGapPadicEmbedding", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifGap

open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p])

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem norm_lt_one_of_valuation_lt_one {x : F} (hx : (placeAt φ).valuation F x < 1) : ‖φ x‖ < 1 := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (placeAt φ) x hx.le
  have hd : ‖φ ((d : 𝓞 F) : F)‖ = 1 := le_antisymm (norm_int_le_one φ _) (not_lt.1 d.2)
  have hdv : (placeAt φ).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F)) ≤ 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one _ _
  have hn : (placeAt φ).intValuation n < 1 := by
    have h0 : (placeAt φ).valuation F (algebraMap (𝓞 F) F n) < 1 := by
      rw [← hnd, map_mul]
      exact (mul_le_of_le_one_right' hdv).trans_lt hx
    rwa [HeightOneSpectrum.valuation_of_algebraMap] at h0
  have hnm : ‖φ (n : F)‖ < 1 := (mem_placeAt φ n).1 ((HeightOneSpectrum.intValuation_lt_one_iff_mem _ n).1 hn)
  have h2 := congrArg (fun t => ‖φ t‖) hnd
  simp only [map_mul, norm_mul] at h2
  have h3 : ‖φ x‖ * ‖φ ((d : 𝓞 F) : F)‖ = ‖φ (n : F)‖ := h2
  rw [hd, mul_one] at h3
  rw [h3]; exact hnm

theorem exists_unif_norm_gap : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]),
    ∃ ϖ : F, 0 < ‖φ ϖ‖ ∧ ‖φ ϖ‖ < 1 ∧ ∀ c : F, ‖φ c‖ < 1 → ‖φ c‖ ≤ ‖φ ϖ‖ := by
  intro p _ F _ _ φ
  set v := (placeAt φ).valuation F with hv
  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F (placeAt φ)
  have hϖ1 : v ϖ < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  refine ⟨ϖ, norm_pos_iff.2 ((map_ne_zero φ).2 hϖ0), norm_lt_one_of_valuation_lt_one φ hϖ1, fun c hc => ?_⟩
  by_cases hc0 : c = 0
  · rw [hc0, map_zero, norm_zero]; exact norm_nonneg _
  have hvc : v c < 1 := by
    by_contra hge
    rw [not_lt] at hge
    have hinv : v c⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ hge
    have h1 := GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one φ hinv
    rw [map_inv₀, norm_inv] at h1
    have hpos : 0 < ‖φ c‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hc0)
    have := (inv_le_one₀ hpos).1 h1
    exact absurd hc (not_lt.2 this)
  have hq : v (c / ϖ) ≤ 1 := by
    rw [map_div₀, hϖ]
    exact div_le_one_of_le₀ (le_exp_neg_one_of_lt_one hvc) zero_le'
  have h1 := GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one φ hq
  rw [map_div₀, norm_div] at h1
  have hpos : 0 < ‖φ ϖ‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hϖ0)
  exact (div_le_one hpos).1 h1

end GlobalTheory.UnifGap

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserNormGapPadicEmbedding =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisTer =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisTer", "h": "module\n\npublic import Mathlib.Analysis.Normed.Field.Instances\npublic import Mathlib.NumberTheory.Padics.Complex\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory.SingleStatement

theorem main : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {ι : Type} (s : Finset ι) (g : ι → ℂ_[p]) {r : ℝ},
    (0 : ℝ) ≤ r → (∀ k ∈ s, ‖g k‖ ≤ r) → ‖∑ k ∈ s, g k‖ ≤ r := by
  intro p _ ι s g r hr hg
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : ‖g a‖ ≤ r := hg a (Finset.mem_insert_self a s)
    have h2 : ‖∑ k ∈ s, g k‖ ≤ r := ih (fun k hk => hg k (Finset.mem_insert_of_mem hk))
    exact (PadicComplex.isNonarchimedean p (g a) (∑ k ∈ s, g k)).trans (max_le h1 h2)

end GlobalTheory.SingleStatement
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisTer =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupLatticeRationalFormMemLocalUnitBall =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupLatticeRationalFormMemLocalUnitBall", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValCCuspOfSmul\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGoodOfBddAll\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

set_option autoImplicit false
noncomputable section



namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_locBall_of_mem_MK : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f : NX.FmK S ((j : ℕ) + 1), (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK → f ∈ locBall YS fw iC b j := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j f hf
  intro z
  obtain ⟨hwk, hb⟩ := ((YS.fi j).mkK _).1 hf
  obtain ⟨T, io, k, hk, y, u, hy, hu, hval⟩ := PtC.exists_valC z (wtA (κ j)) (κ j).n
  obtain ⟨e, ho⟩ := GlobalTheory.ReadingOver.overLa_placeAt _ _ (embC YS iC b) T io k hk
  let v : T0.PtM ((j : ℕ) + 1) (placeC YS iC b) :=
    ⟨vAtV (PtV.mk (cls := algCls (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c) (PY := Unit) (lies := fun _ _ _ _ => True)
      (placeC YS iC b) ho y hy () trivial), ⟨_, rfl⟩⟩
  obtain ⟨w, hw⟩ := (fw.pt j (placeC YS iC b)).surjective v
  have h1 := hb (placeC YS iC b) w
  have e1 : (⟨(YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1, hwk⟩ : (Rl.FW j).WK) = fw.e j (cuspOf YS fw j f) :=
    Subtype.ext (e_cuspOf YS fw j f).symm
  rw [e1, fw.nrm_eq, hw] at h1
  have h2 := (T0.nrmM_le_one_iff _ _ v _).1 h1
  have h3 := (GlobalTheory.GoodPtsModel.inV_iff_nval T ho.1 (evI y (cuspOf YS fw j f : T0.R ((j : ℕ) + 1)))).2 h2
  rw [hval _ (cuspOf_mem_sec YS fw j f), norm_mul, hu, one_mul]
  exact (hk.int _).2 h3

end GlobalTheory.GeoTie
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupLatticeRationalFormMemLocalUnitBall =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitBallFiniteUnramifiedDescentComplexPadic =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitBallFiniteUnramifiedDescentComplexPadic", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValCCuspOfSmul\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidue\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCp\nimport Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct



namespace GlobalTheory.GeoTie.BallDescent

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Sum

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} {iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]} {b : Bool}
  (j : Fin D.R.m)

theorem valC_cuspOf_sum (z : FrC YS iC b ((j : ℕ) + 1)) {ι : Type} (s : Finset ι) (g : ι → NX.FmK S ((j : ℕ) + 1)) :
    valC z (cuspOf YS fw j (∑ t ∈ s, g t) : T0.R ((j : ℕ) + 1)) =
      ∑ t ∈ s, valC z (cuspOf YS fw j (g t) : T0.R ((j : ℕ) + 1)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, map_zero, ZeroMemClass.coe_zero, valC_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add (f := _), Submodule.coe_add, valC_add, ih]

end Sum

theorem ball_descent : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) → ∀ (F' : Type) [Field F'] [NumberField F'] [Algebra S.Ks F'] (φ' : F' →+* ℂ_[D.ntw.l i]), (∀ a, φ' (algebraMap S.Ks F' a) = embS S iC b a) → (∀ a : S.Ks, vLa (placeAt φ') (algebraMap S.Ks F' a) = vLa (placeAt (embS S iC b)) a) → ∀ (n : ℕ) (a : Fin n → F') (f : Fin n → NX.FmK S ((j : ℕ) + 1)), (∀ z : Pts YS iC b ((j : ℕ) + 1), ‖∑ s, φ' (a s) * valC z.1 (cuspOf YS fw j (f s) : T0.R ((j : ℕ) + 1))‖ ≤ 1) → ∃ (m : ℕ) (β : Fin m → F') (g : Fin m → NX.FmK S ((j : ℕ) + 1)), (∀ t, ‖φ' (β t)‖ ≤ 1) ∧ (∀ t, g t ∈ locBall YS fw iC b j) ∧ ∑ s, a s ⊗ₜ[S.Ks] f s = ∑ t, β t ⊗ₜ[S.Ks] g t := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _hiC b j hball F' _ _ _ φ' hφ' hv n a f hz
  have := GlobalTheory.SupDescent.liesOver (K := S.Ks) (K' := F') (la := placeAt (embS S iC b)) (la' := placeAt φ') hv
  obtain ⟨d, bb, hb1, hb2⟩ := GlobalTheory.SupDescent.exists_residue_basis (la := placeAt (embS S iC b)) (la' := placeAt φ')
  choose c hc0 hcB using fun s => hball (f s)
  choose x ρ hρ hx using fun s => GlobalTheory.SupDescent.exists_approx (K := S.Ks) (K' := F') hv hb2 (a s) (hc0 s)
  let F : Fin d → NX.FmK S ((j : ℕ) + 1) := fun t => ∑ s, x s t • f s
  have hmem : ∀ g : NX.FmK S ((j : ℕ) + 1), (cuspOf YS fw j g : T0.R ((j : ℕ) + 1)) ∈
      sec (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (wtA (κ j)) (κ j).n := cuspOf_mem_sec YS fw j
  have hF : ∀ t, F t ∈ locBall YS fw iC b j := by
    intro t z
    obtain ⟨T, io, k, hR, y, u, hT, hu, hval⟩ := PtC.exists_valC z (wtA (κ j)) (κ j).n
    rw [hval _ (hmem _), norm_mul, hu, one_mul]
    let io' : S.Ks →+* T.Fr := io.comp (eKs YS).toRingHom
    have hR' : IsReading (embS S iC b) T io' k :=
      ⟨fun a => (hR.comp (eKs YS a)).trans (embC_eKs YS iC b a), hR.int⟩
    obtain ⟨e, ho⟩ := GlobalTheory.ReadingOver.overLa_placeAt_of_isReading (embS S iC b) hR'
    refine (hR.int _).2 ?_
    refine GlobalTheory.SupDescent.inV_of_forall_emb (K := S.Ks) (K' := F') hb1 hT ho
      (fun t => evI y (cuspOf YS fw j (F t) : T0.R ((j : ℕ) + 1))) ?_ t
    intro T' i e' σ e'' he' hi hT' hσ ho'
    obtain ⟨y₁, ψ, hψ, hmap⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange _ _ _ _ _ _ T T' io y i e' he' hi
    obtain ⟨k', hk'⟩ := GlobalTheory.GeoTie.ReadExist.exists_isReading _ F' φ' T' σ e'' ho' hT'
    have hR₁ : IsReading (embC YS iC b) T' (i.comp io) k' := by
      refine ⟨fun a => ?_, hk'.int⟩
      obtain ⟨a0, rfl⟩ := (eKs YS).surjective a
      rw [embC_eKs, ← hφ' a0, ← hk'.comp, hσ a0]
      rfl
    obtain ⟨z', hz'⟩ := PtC.exists_of_reading hR₁ y₁ hT'
    have h4 : ∀ g : NX.FmK S ((j : ℕ) + 1),
        k' (i (evI y (cuspOf YS fw j g : T0.R ((j : ℕ) + 1)))) = valC z'.1 (cuspOf YS fw j g : T0.R ((j : ℕ) + 1)) := by
      intro g
      have h5 : i (evI y (cuspOf YS fw j g : T0.R ((j : ℕ) + 1))) = evI y₁ (cuspOf YS fw j g : T0.R ((j : ℕ) + 1)) := by
        letI := io.toAlgebra
        letI := (i.comp io).toAlgebra
        exact (DFunLike.congr_fun hψ _).symm.trans (GlobalTheory.FlagTan.evR_frMap (hmem g).1 hmap).symm
      rw [h5, hz' _ _ _ (hmem g)]
    refine (hk'.int _).1 ?_

    rw [map_sum]
    simp only [map_mul, hk'.comp, h4]
    have hid : ∑ t, φ' (bb t : F') * valC z'.1 (cuspOf YS fw j (F t) : T0.R ((j : ℕ) + 1)) =
        ∑ s, φ' (a s) * valC z'.1 (cuspOf YS fw j (f s) : T0.R ((j : ℕ) + 1)) -
          ∑ s, φ' (ρ s) * valC z'.1 (cuspOf YS fw j (c s • f s) : T0.R ((j : ℕ) + 1)) := by
      rw [eq_sub_iff_add_eq]
      simp only [F, valC_cuspOf_sum YS fw j, valC_cuspOf_smul YS fw j, Finset.mul_sum]
      rw [Finset.sum_comm, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hx s]

      simp only [map_add (f := _), map_sum, map_mul, hφ', Finset.sum_mul, add_mul]
      congr 1
      · exact Finset.sum_congr rfl fun t _ => by ring
      · ring
    rw [hid]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz z') ?_)
    rw [norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun s _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one φ' (hρ s)) (norm_nonneg _) (hcB s z')
  refine ⟨d + n, Fin.append (fun t => (bb t : F')) ρ, Fin.append F fun s => c s • f s, fun t => ?_, fun t => ?_, ?_⟩
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · rw [Fin.append_left]; exact norm_int_le_one φ' (bb t)
    · rw [Fin.append_right]; exact GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one φ' (hρ t)
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · rw [Fin.append_left]; exact hF t
    · rw [Fin.append_right]; exact hcB t
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have e : ∀ s, a s = ∑ t, x s t • (bb t : F') + c s • ρ s := fun s => by
      rw [hx s]; simp only [Algebra.smul_def]; rw [mul_comm (algebraMap _ _ (c s))]
    have h1 : ∀ t s, (bb t : F') ⊗ₜ[S.Ks] (x s t • f s) = (x s t • (bb t : F')) ⊗ₜ[S.Ks] f s :=
      fun t s => (TensorProduct.smul_tmul _ _ _).symm
    have h2 : ∀ s, ρ s ⊗ₜ[S.Ks] (c s • f s) = (c s • ρ s) ⊗ₜ[S.Ks] f s := fun s => (TensorProduct.smul_tmul _ _ _).symm
    simp only [F, TensorProduct.tmul_sum, h1, h2]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← TensorProduct.sum_tmul, ← TensorProduct.add_tmul, ← e s]

end GlobalTheory.GeoTie.BallDescent
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitBallFiniteUnramifiedDescentComplexPadic =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsFurther =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsFurther", "h": "module\n\nimport Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsSat\npublic import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory.ScalarMultipleMembership

theorem exists_smul_mem {Ks WL : Type} [Field Ks] [NumberField Ks] [AddCommGroup WL] [Module Ks WL]
    [Module (NumberField.RingOfIntegers Ks) WL]
    [IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL]
    (M : Submodule (NumberField.RingOfIntegers Ks) WL) (x : WL)
    (hx : x ∈ Submodule.span Ks (M : Set WL)) :
    ∃ a : NumberField.RingOfIntegers Ks, a ≠ 0 ∧ a • x ∈ M := by
  apply Formalism.L2.SG.Pf.LatEx.exists_smul_mem_of_mem_span <;> assumption

theorem main {LL Ks WL G : Type} [inst : Field LL] [NumberField LL] [inst_2 : Field Ks] [inst_3 : NumberField Ks] [inst_4 : Algebra Ks LL] [inst_5 : AddCommGroup WL] [inst_6 : Module LL WL] [inst_7 : Module Ks WL] [IsScalarTower Ks LL WL] [inst_9 : Module (NumberField.RingOfIntegers Ks) WL] [inst_10 : IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL] {W : (LL →+* ℂ) → Type} [inst_11 : (σ : LL →+* ℂ) → NormedAddCommGroup (W σ)] [inst_12 : (σ : LL →+* ℂ) → InnerProductSpace ℂ (W σ)] [inst_13 : Group G] (Φ : Formalism.IndefR.Arith.FormsL LL Ks WL W G)
    (h : Submodule.span Ks (↑(Formalism.IndefR.Arith.FormsL.MK Φ) : Set WL) = Formalism.IndefR.Arith.FormsL.WK Φ) :
    ∀ x ∈ Formalism.IndefR.Arith.FormsL.WK Φ, ∃ (a : NumberField.RingOfIntegers Ks), a ≠ (0 : NumberField.RingOfIntegers Ks) ∧ a • x ∈ Formalism.IndefR.Arith.FormsL.MK Φ := by
  intro x hx
  rw [← h] at hx
  exact exists_smul_mem _ x hx

end GlobalTheory.ScalarMultipleMembership
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsFurther =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightVectorRealizationExists =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightVectorRealizationExists", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValCCuspOfSmul\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCuspFormsFullLattice\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsFurther\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct



namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_smul_mem_locBall : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK → f ∈ locBall YS fw iC b j) → (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j hball f
  have hfull := GlobalTheory.GoodLat.Obj.mkFull_of_tie fw j
  have hwk : (YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (Rl.FW j).WK :=
    ((YS.fi j).wk _).1 (show ↥(S.A ((j : ℕ) + 1)).WK from f).2
  obtain ⟨a, ha, hamk⟩ := _root_.GlobalTheory.ScalarMultipleMembership.main (Rl.FW j) hfull.2 _ hwk
  refine ⟨(YS.fi j).eK.symm (a : T0.Q.c.F), ?_, hball _ ?_⟩
  · intro h
    apply ha
    have : ((a : T0.Q.c.F)) = 0 := by
      have := congrArg (YS.fi j).eK h
      simpa using this
    exact_mod_cast this
  · rw [(YS.fi j).mkK]
    have h1 : ((show ↥(S.A ((j : ℕ) + 1)).WK from (YS.fi j).eK.symm (a : T0.Q.c.F) • f)).1 =
        (YS.fi j).eK.symm (a : T0.Q.c.F) • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 := rfl
    rw [h1, ← algebraMap_smul D.what₂.LL, map_smul, ← (YS.fi j).eK_LL, RingEquiv.apply_symm_apply, algebraMap_smul,
      algebraMap_smul]
    exact hamk

end GlobalTheory.GeoTie
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightVectorRealizationExists =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSumLeOfLe =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSumLeOfLe", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValCCuspOfSmul\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisRationalFormsLocalUnitBall\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteUnramifiedApproximationPadic\npublic import Mathlib.Analysis.Normed.Field.Instances\npublic import Mathlib.NumberTheory.NumberField.Basic\npublic import Mathlib.NumberTheory.Padics.Complex\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserNormGapPadicEmbedding\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisTer\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneTmulMemSupLatticeOfMemLocalUnitBall\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupLatticeRationalFormMemLocalUnitBall\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitBallFiniteUnramifiedDescentComplexPadic\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightVectorRealizationExists\nimport Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormEqOfMemClosure\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct



namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Core

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool)
  (j : Fin D.R.m)

theorem fieldRange_embC : (embC YS iC b).fieldRange = (embS S iC b).fieldRange := by
  ext y
  simp only [RingHom.mem_fieldRange]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨c, rfl⟩ := (eKs YS).surjective a
    exact ⟨c, (embC_eKs YS iC b c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨eKs YS c, embC_eKs YS iC b c⟩

theorem kurAt_iff (a : FractionRing (D.ntw.O i)) : a ∈ kurAt YS iC b ↔ iC a ∈ kurC (embS S iC b) := by
  rw [kurAt, Subfield.mem_comap, kurC_congr _ (fieldRange_embC YS iC b)]

def coef {n : ℕ} (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))) (x : NX.Fm S i ((j : ℕ) + 1) b) (s : Fin n) :
    FractionRing (D.ntw.O i) :=
  (B.baseChange (NX.KB S i b)).repr x s

variable {b j} in
theorem coef_add {n : ℕ} (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))) (x y : NX.Fm S i ((j : ℕ) + 1) b)
    (s : Fin n) : coef b j B (x + y) s = coef b j B x s + coef b j B y s := by
  exact Finsupp.ext_iff.1 (map_add (B.baseChange (NX.KB S i b)).repr x y) s

variable {b j} in
theorem coef_neg {n : ℕ} (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))) (x : NX.Fm S i ((j : ℕ) + 1) b)
    (s : Fin n) : coef b j B (-x) s = -coef b j B x s := by
  exact Finsupp.ext_iff.1 (map_neg (B.baseChange (NX.KB S i b)).repr x) s

variable {b j} in
theorem coef_zero {n : ℕ} (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))) (s : Fin n) :
    coef b j B (0 : NX.Fm S i ((j : ℕ) + 1) b) s = 0 := by
  exact Finsupp.ext_iff.1 (map_zero (B.baseChange (NX.KB S i b)).repr) s

variable {b j} in
theorem coef_tmul {n : ℕ} (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))) (a : NX.KB S i b)
    (f : NX.FmK S ((j : ℕ) + 1)) (s : Fin n) :
    coef b j B (show NX.Fm S i ((j : ℕ) + 1) b from a ⊗ₜ[S.Ks] f) s =
      (show FractionRing (D.ntw.O i) from NX.ιK S i b (B.repr f s)) * (show FractionRing (D.ntw.O i) from a) := by
  exact Module.Basis.baseChange_repr_tmul (b := B) (x := a) (y := f) (i := s)

theorem coef_mem_kurAt {n : ℕ} (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1)))
    {x : NX.Fm S i ((j : ℕ) + 1) b} (hx : x ∈ ratForms S ((j : ℕ) + 1) b (kurAt YS iC b)) (s : Fin n) :
    coef b j B x s ∈ kurAt YS iC b := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, f, rfl⟩ := hx
    rw [coef_tmul]
    refine (kurAt YS iC b).mul_mem ?_ ha
    rw [kurAt_iff]
    exact mem_kurC (embS S iC b) (B.repr f s)
  | zero => rw [coef_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [coef_add]; exact add_mem hx hy
  | neg x _ hx => rw [coef_neg]; exact neg_mem hx

end Core

end GlobalTheory.GeoTie

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Core2

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool)
  (j : Fin D.R.m)

def oneK (f : NX.FmK S ((j : ℕ) + 1)) : NX.Fm S i ((j : ℕ) + 1) b := (1 : NX.KB S i b) ⊗ₜ[S.Ks] f

theorem eq_sum_coef {n : ℕ} (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))) (x : NX.Fm S i ((j : ℕ) + 1) b) :
    x = ∑ s, coef b j B x s • oneK b j (B s) := by
  have h := (B.baseChange (NX.KB S i b)).sum_repr x
  simp only [Module.Basis.baseChange_apply] at h
  exact h.symm

theorem valAt_eq_sum {n : ℕ} (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))) (x : NX.Fm S i ((j : ℕ) + 1) b)
    (z : FrC YS iC b ((j : ℕ) + 1)) :
    valAt YS fw j z x = ∑ s, iC (coef b j B x s) * valC z (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1)) := by
  conv_lhs => rw [eq_sum_coef b j B x]

  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [valAt_smul]
  congr 1
  have h1 : iC (1 : NX.KB S i b) = 1 := map_one iC
  exact (valAt_tmul YS fw j z 1 (B s)).trans (by rw [h1, one_mul])

theorem mem_span_locBall
    (hiC : ∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range)
    (hC1 : ∃ (n : ℕ) (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))), (∀ s, B s ∈ locBall YS fw iC b j) ∧
      ∀ g ∈ locBall YS fw iC b j, ∀ s, ‖embS S iC b (B.repr g s)‖ ≤ 1)
    (hC2 : ∀ (F' : Type) [Field F'] [NumberField F'] [Algebra S.Ks F'] (φ' : F' →+* ℂ_[D.ntw.l i]), (∀ a, φ' (algebraMap S.Ks F' a) = embS S iC b a) → (∀ a : S.Ks, vLa (placeAt φ') (algebraMap S.Ks F' a) = vLa (placeAt (embS S iC b)) a) → ∀ (n : ℕ) (a : Fin n → F') (f : Fin n → NX.FmK S ((j : ℕ) + 1)), (∀ z : Pts YS iC b ((j : ℕ) + 1), ‖∑ s, φ' (a s) * valC z.1 (cuspOf YS fw j (f s) : T0.R ((j : ℕ) + 1))‖ ≤ 1) → ∃ (m : ℕ) (β : Fin m → F') (g : Fin m → NX.FmK S ((j : ℕ) + 1)), (∀ t, ‖φ' (β t)‖ ≤ 1) ∧ (∀ t, g t ∈ locBall YS fw iC b j) ∧ ∑ s, a s ⊗ₜ[S.Ks] f s = ∑ t, β t ⊗ₜ[S.Ks] g t)
    (x : NX.Fm S i ((j : ℕ) + 1) b) (hx : x ∈ urBall YS fw iC b j 1) :
    x ∈ Submodule.span (D.ntw.O i) (oneK b j '' locBall YS fw iC b j) := by
  obtain ⟨n, B, hB, hBc⟩ := hC1
  have hkur : ∀ s, iC (coef b j B x s) ∈ kurC (embS S iC b) := fun s =>
    (kurAt_iff YS iC b _).1 (coef_mem_kurAt YS iC b j B hx.1 s)
  have hval : ∀ z : Pts YS iC b ((j : ℕ) + 1),
      ‖∑ s, iC (coef b j B x s) * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1))‖ ≤ 1 := fun z => by
    rw [← valAt_eq_sum]
    exact hx.2 z
  have hle : ∀ s, ‖iC (coef b j B x s)‖ ≤ 1 := by
    by_contra hne
    push_neg at hne
    obtain ⟨s1, hs1⟩ := hne
    obtain ⟨s0, -, hs0⟩ := Finset.exists_max_image Finset.univ (fun s => ‖iC (coef b j B x s)‖) ⟨s1, Finset.mem_univ _⟩
    have hM : 1 < ‖iC (coef b j B x s0)‖ := hs1.trans_le (hs0 s1 (Finset.mem_univ _))
    obtain ⟨c, hc⟩ := (GlobalTheory.KurValue.kurC_value_residue (D.ntw.l i) S.Ks (embS S iC b)).1 _ (hkur s0)
    have hcpos : 0 < ‖embS S iC b c‖ := by rw [← hc]; linarith
    have hc0 : embS S iC b c ≠ 0 := norm_pos_iff.1 hcpos
    set w : Fin n → ℂ_[D.ntw.l i] := fun s => iC (coef b j B x s) / embS S iC b c with hw
    have hw1 : ∀ s, ‖w s‖ ≤ 1 := fun s => by
      rw [hw, norm_div, ← hc, div_le_one (by linarith)]
      exact hs0 s (Finset.mem_univ _)
    have hw0 : ‖w s0‖ = 1 := by
      rw [hw, norm_div, ← hc, div_self (by linarith)]
    have hwk : ∀ s, w s ∈ kurC (embS S iC b) := fun s => div_mem (hkur s) (mem_kurC _ c)
    obtain ⟨ϖ, hϖ0, hϖ1, hϖ⟩ := _root_.GlobalTheory.UnifGap.exists_unif_norm_gap (D.ntw.l i) S.Ks (embS S iC b)
    set r := ‖embS S iC b ϖ‖ with hr
    have hcr : ‖embS S iC b c‖⁻¹ ≤ r := by
      have h1 : ‖embS S iC b c⁻¹‖ < 1 := by
        rw [map_inv₀, norm_inv, ← hc]
        exact inv_lt_one_of_one_lt₀ hM
      have := hϖ c⁻¹ h1
      rwa [map_inv₀, norm_inv] at this
    have hsum : ∀ z : Pts YS iC b ((j : ℕ) + 1),
        ‖∑ s, w s * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1))‖ ≤ r := fun z => by
      have e : ∑ s, w s * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1)) =
          (∑ s, iC (coef b j B x s) * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1))) * (embS S iC b c)⁻¹ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [hw]
        rw [div_eq_mul_inv]
        ring
      rw [e, norm_mul, norm_inv]
      calc _ ≤ 1 * ‖embS S iC b c‖⁻¹ := mul_le_mul_of_nonneg_right (hval z) (by positivity)
        _ ≤ r := by rw [one_mul]; exact hcr
    obtain ⟨F', _, _, _, φ', hφ', hunr, a', ha'⟩ := _root_.GlobalTheory.KurApprox.kur_approx (D.ntw.l i) S.Ks (embS S iC b) n w hwk r hϖ0
    have hsum' : ∀ z : Pts YS iC b ((j : ℕ) + 1),
        ‖∑ s, φ' (a' s) * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1))‖ ≤ r := fun z => by
      have e : ∑ s, φ' (a' s) * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1)) =
          ∑ s, w s * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1)) +
            ∑ s, (φ' (a' s) - w s) * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hsum z) ?_)
      refine _root_.GlobalTheory.SingleStatement.main _ _ hϖ0.le fun s _ => ?_
      rw [norm_mul]
      calc _ ≤ r * 1 := by
            refine mul_le_mul ?_ (hB s z) (norm_nonneg _) hϖ0.le
            rw [norm_sub_rev]
            exact (ha' s).le
        _ = r := mul_one r
    have hϖ' : φ' (algebraMap S.Ks F' ϖ) ≠ 0 := by rw [hφ']; exact norm_pos_iff.1 hϖ0
    obtain ⟨m, β, g, hβ, hg, heq⟩ := hC2 F' φ' hφ' hunr n (fun s => a' s * (algebraMap S.Ks F' ϖ)⁻¹) (fun s => B s)
      (fun z => by
        have e : ∑ s, φ' (a' s * (algebraMap S.Ks F' ϖ)⁻¹) * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1)) =
            (∑ s, φ' (a' s) * valC z.1 (cuspOf YS fw j (B s) : T0.R ((j : ℕ) + 1))) * (φ' (algebraMap S.Ks F' ϖ))⁻¹ := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [map_mul, map_inv₀]
          ring
        rw [e, norm_mul, norm_inv, hφ', ← hr]
        rw [← div_eq_mul_inv, div_le_one hϖ0]
        exact hsum' z)
    have hco := congrArg (fun t => (B.baseChange F').repr t s0) heq

    simp only [map_sum, Finset.sum_apply', Module.Basis.baseChange_repr_tmul,
    Module.Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hco
    have h1 : ‖φ' (a' s0 * (algebraMap S.Ks F' ϖ)⁻¹)‖ ≤ 1 := by

      rw [hco, map_sum]
      refine _root_.GlobalTheory.SingleStatement.main _ _ zero_le_one fun t _ => ?_
      rw [Algebra.smul_def, map_mul, hφ', norm_mul]
      calc _ ≤ 1 * 1 := mul_le_mul (hBc (g t) (hg t) s0) (hβ t) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have h2 : ‖φ' (a' s0)‖ ≤ r := by
      rw [map_mul, map_inv₀, hφ', norm_mul, norm_inv, ← hr, ← div_eq_mul_inv, div_le_one hϖ0] at h1
      exact h1
    have h3 : ‖w s0‖ ≤ r := by
      have := IsUltrametricDist.norm_add_le_max (w s0 - φ' (a' s0)) (φ' (a' s0))
      rw [sub_add_cancel] at this
      exact this.trans (max_le (ha' s0).le h2)
    linarith
  rw [eq_sum_coef b j B x]
  refine Submodule.sum_mem _ fun s _ => ?_
  obtain ⟨o, ho⟩ := (hiC (coef b j B x s)).1 (hle s)
  rw [← ho, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨B s, hB s, rfl⟩)

end Core2

end GlobalTheory.GeoTie

theorem GlobalTheory.GeoTie.supDescent_side : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), SupDescent YS fw iC b j := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC hiC b j
  have hA := _root_.GlobalTheory.GeoTie.mem_locBall_of_mem_MK D Γ Pl0 I0 T1 A3 T0 Rl cG S YS κ v₀ fw i iC hiC b j
  have hbdd := _root_.GlobalTheory.GeoTie.exists_smul_mem_locBall D Γ Pl0 I0 T1 A3 T0 Rl cG S YS κ v₀ fw i iC hiC b j hA
  have h1 : iC (1 : NX.KB S i b) = 1 := map_one iC
  unfold SupDescent
  apply le_antisymm
  · rw [NX.Bsup, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    apply Submodule.subset_span
    refine ⟨tmul_mem_ratForms (b := b) (kurAt YS iC b).one_mem x, fun z => ?_⟩
    rw [valAt_tmul, h1, one_mul]
    exact hA x hx z
  · rw [Submodule.span_le]
    intro x hx
    have h := mem_span_locBall YS fw iC b j hiC (_root_.GlobalTheory.GeoTie.locBall_basis_exists D Γ Pl0 I0 T1 A3 T0 Rl cG S YS κ v₀ fw i iC hiC b j hbdd) (_root_.GlobalTheory.GeoTie.BallDescent.ball_descent D Γ Pl0 I0 T1 A3 T0 Rl cG S YS κ v₀ fw i iC hiC b j hbdd) x hx
    refine (Submodule.span_le.2 ?_) h
    rintro _ ⟨f, hf, rfl⟩
    exact _root_.GlobalTheory.GeoTie.one_tmul_mem_Bsup D Γ Pl0 I0 T1 A3 T0 Rl cG S YS κ v₀ fw i iC hiC b j f hf
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSumLeOfLe =====
