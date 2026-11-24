module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.IntStruct


open MvPolynomial in
theorem exists_coord_eq_sum_coeff {σ : Type} {d : ℕ} (V : Submodule ℂ (MvPolynomial σ ℂ)) (B : Module.Basis (Fin d) ℂ V)
    (i : Fin d) : ∃ (s : Finset (σ →₀ ℕ)) (a : s → ℂ), ∀ v : V,
      B.repr v i = ∑ m : s, a m * (v : MvPolynomial σ ℂ).coeff m.1 := by
  classical
  let s : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun j => ((B j : V) : MvPolynomial σ ℂ).support
  let R : V →ₗ[ℂ] (s → ℂ) := LinearMap.pi fun m => (lcoeff ℂ m.1).comp V.subtype
  have hR : LinearMap.ker R = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun v hv => ?_
    have h0 : ∀ m : s, (v : MvPolynomial σ ℂ).coeff m.1 = 0 := fun m => congrFun hv m
    refine Subtype.ext (MvPolynomial.ext _ _ fun m => ?_)
    change (v : MvPolynomial σ ℂ).coeff m = 0
    by_cases hm : m ∈ s
    · exact h0 ⟨m, hm⟩
    · have hv' : (v : MvPolynomial σ ℂ) = ∑ j, B.repr v j • ((B j : V) : MvPolynomial σ ℂ) := by
        calc (v : MvPolynomial σ ℂ) = ((∑ j, B.repr v j • B j : V) : MvPolynomial σ ℂ) := by rw [B.sum_repr v]
          _ = _ := by rw [Submodule.coe_sum]; rfl
      rw [hv', coeff_sum]
      simp only [MvPolynomial.coeff_smul]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : m ∉ ((B j : V) : MvPolynomial σ ℂ).support := fun h =>
        hm (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, h⟩)
      rw [notMem_support_iff.1 this, smul_zero]
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hR
  refine ⟨s, fun m => B.repr (L (Pi.single m 1)) i, fun v => ?_⟩
  have e1 : B.repr v i = ((B.coord i).comp L) (R v) := by
    rw [LinearMap.comp_apply, ← LinearMap.comp_apply L R, hL, LinearMap.id_apply, Module.Basis.coord_apply]
  rw [e1, LinearMap.pi_apply_eq_sum_univ ((B.coord i).comp L) (R v)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hs : (fun j => if m = j then (1 : ℂ) else 0) = Pi.single m 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [hs, smul_eq_mul, mul_comm]
  rfl

end GlobalTheory.IntStruct

end
