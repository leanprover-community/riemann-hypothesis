module

public import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriangularMul
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetIndepStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum


noncomputable section

namespace GlobalTheory.CoefLin

open MvPolynomial Formalism.L2.Pj

variable {σ : Type} (F : IntermediateField ℚ ℂ) (lam : ℂ →ₗ[F] F)

def coefFun (p : MvPolynomial σ ℂ) : MvPolynomial σ F := ∑ m ∈ p.support, monomial m (lam (p.coeff m))

theorem coeff_coefFun (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) : (coefFun F lam p).coeff m = lam (p.coeff m) := by
  classical
  rw [coefFun, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

def coefMap : MvPolynomial σ ℂ →+ MvPolynomial σ F where
  toFun := coefFun F lam
  map_zero' := by
    ext m
    simp only [coeff_coefFun, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero]
  map_add' p q := by
    ext m
    simp only [coeff_coefFun, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]

variable {F lam}

theorem coeff_coefMap (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    (coefMap F lam p).coeff m = lam (p.coeff m) :=
  coeff_coefFun F lam p m

theorem coefMap_monomial (m : σ →₀ ℕ) (c : ℂ) :
    coefMap F lam (monomial m c) = lam c • monomial m (1 : F) := by
  ext m'
  rw [coeff_coefMap, MvPolynomial.coeff_smul, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

theorem coefMap_smul_map (c : ℂ) (R : MvPolynomial σ F) :
    coefMap F lam (c • map (algebraMap F ℂ) R) = lam c • R := by
  ext m
  rw [coeff_coefMap, MvPolynomial.coeff_smul, coeff_map, MvPolynomial.coeff_smul, smul_eq_mul, smul_eq_mul]
  have : c * algebraMap F ℂ (R.coeff m) = R.coeff m • c := by
    rw [Algebra.smul_def, mul_comm]
  rw [this, map_smul, smul_eq_mul, mul_comm]

theorem coefMap_comm (Φ : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) (Ψ : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (h : ∀ Q, Φ (map (algebraMap F ℂ) Q) = map (algebraMap F ℂ) (Ψ Q)) (p : MvPolynomial σ ℂ) :
    coefMap F lam (Φ p) = Ψ (coefMap F lam p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm : (monomial m c : MvPolynomial σ ℂ) = c • map (algebraMap F ℂ) (monomial m (1 : F)) := by
      rw [map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul, h, coefMap_smul_map, ← hm, coefMap_monomial, map_smul]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]

variable {T : Type} (r : T → ℕ) (n : ℕ)

theorem lap_map (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ')) (Q : MvPolynomial (Letter T r n) F) :
    lap r n ℂ 1 τ τ' a a' (map (algebraMap F ℂ) Q) = map (algebraMap F ℂ) (lap r n F 1 τ τ' a a' Q) := by

  simp only [lap, LinearMap.sum_apply, map_sum, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp [pderiv_map]

theorem rowShift_map (σ₀ : T) (i i' : Fin (r σ₀)) (t : F) (Q : MvPolynomial (Letter T r n) F) :
    rowShift r n ℂ σ₀ i i' (t : ℂ) (map (algebraMap F ℂ) Q) = map (algebraMap F ℂ) (rowShift r n F σ₀ i i' t Q) := by
  have key : (rowShift r n ℂ σ₀ i i' (t : ℂ)).toRingHom.comp (map (algebraMap F ℂ)) =
      (map (algebraMap F ℂ)).comp (rowShift r n F σ₀ i i' t).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [rowShift]
    · intro ℓ
      simp only [rowShift, RingHom.coe_comp, Function.comp_apply, map_X, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, aeval_X]
      split_ifs <;> simp
  exact RingHom.congr_fun key Q

end GlobalTheory.CoefLin

namespace GlobalTheory.SingleDatum

open MvPolynomial Formalism.L2.Pj GlobalTheory.CoefLin

theorem HHa_coefLin : ∀ (T : Type) (r : T → ℕ) (n : ℕ) (cj : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    (F : IntermediateField ℚ ℂ) (lam : ℂ →ₗ[F] F), ∀ P ∈ HHa r n ℂ cj isX a, ∃ P' ∈ HHa r n F cj isX a,
      ∀ mo, P'.coeff mo = lam (P.coeff mo) := by
  intro T r n cj isX a F lam P hP
  obtain ⟨hH, hR, hD⟩ := hP
  refine ⟨coefMap F lam P, ⟨?_, ?_, ?_⟩, coeff_coefMap P⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at hH ⊢
    intro τ hτ i i'
    rw [← coefMap_comm (lap r n ℂ 1 τ (cj τ) i i') (lap r n F 1 τ (cj τ) i i') (lap_map r n τ (cj τ) i i') P,
      hH τ hτ i i', map_zero]
  · intro σ₀ i i' hii t
    have key := coefMap_comm (lam := lam) (rowShift r n ℂ σ₀ i i' (t : ℂ)).toLinearMap
      (rowShift r n F σ₀ i i' t).toLinearMap (rowShift_map r n σ₀ i i' t) P
    simp only [AlgHom.toLinearMap_apply] at key
    rw [← key, hR σ₀ i i' hii (t : ℂ)]
  · intro m hm σ₀ i
    refine hD m ?_ σ₀ i
    rw [mem_support_iff] at hm ⊢
    intro h0
    apply hm
    rw [coeff_coefMap, h0, map_zero]

end GlobalTheory.SingleDatum

end
