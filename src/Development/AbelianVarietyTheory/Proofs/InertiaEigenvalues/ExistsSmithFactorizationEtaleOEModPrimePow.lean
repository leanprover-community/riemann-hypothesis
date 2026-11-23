module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorization
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmithFormCoefficientRingImageOrPrimeDvdRowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittCompletedTiltColumnsOfRightInverseModPowStatement
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory.SmithQuot

theorem oe_dvr : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsDiscreteValuationRing ↥bk.OE := by
  intro l _ K bk
  haveI : PerfectRing (Cb l) l := GlobalTheory.OEDvr.perfectRing_Cb
  obtain ⟨hdivl, -, -, hfac, -⟩ := GlobalTheory.OEDvr.main l K bk
  have hlW : Irreducible ((l : ℕ) : WCb l) := WittVector.irreducible l (k := Cb l)
  have hlO : (l : WCb l) ∈ bk.OE := natCast_mem _ l
  set π : ↥bk.OE := ⟨(l : WCb l), hlO⟩
  have hπ : ¬ IsUnit π := fun h => hlW.not_isUnit (h.map bk.OE.subtype)
  have hfac' : ∀ x : ↥bk.OE, x ≠ 0 → ∃ k : ℕ, Associated (π ^ k) x := by
    intro x hx
    obtain ⟨k, v, v', hv, hv', hvv, hx'⟩ := hfac x x.2 (fun h => hx (Subtype.ext h))
    refine ⟨k, ⟨⟨⟨v, hv⟩, ⟨v', hv'⟩, Subtype.ext hvv, Subtype.ext (by rw [mul_comm]; exact hvv)⟩, ?_⟩⟩
    apply Subtype.ext
    simp [π, hx']
  have hunit : ∀ x : ↥bk.OE, IsUnit (x : WCb l) → IsUnit x := by
    intro x hx
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    obtain ⟨k, hk⟩ := hfac' x hx0
    rcases k with _ | k
    · exact hk.isUnit_iff.mp (by rw [pow_zero]; exact isUnit_one)
    · exfalso
      obtain ⟨u, hu⟩ := hk
      have : (l : WCb l) ∣ (x : WCb l) := by
        rw [← hu]; exact ⟨(l : WCb l) ^ k * (u : ↥bk.OE), by simp [π, pow_succ]; ring⟩
      exact hlW.not_isUnit (isUnit_of_dvd_unit this hx)
  have hirr : Irreducible π := by
    refine ⟨hπ, ?_⟩
    intro a b hab
    have := hlW.isUnit_or_isUnit (show ((l : ℕ) : WCb l) = (a : WCb l) * (b : WCb l) from congrArg Subtype.val hab)
    exact this.imp (hunit a) (hunit b)
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨π, hirr, fun {x} hx => hfac' x hx⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' n : ℕ) (Q : Matrix (Fin d) (Fin d') (WCb l)) (P : Matrix (Fin d') (Fin d') (WCb l)), 1 ≤ n → (∀ i j, P i j ∈ bk.OE) → (∃ S : Matrix (Fin d') (Fin d) (WCb l), (∀ i j, (l : WCb l) ^ n ∣ (Q * S - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j)) → (∀ v : Fin d' → WCb l, (∀ i, (l : WCb l) ^ n ∣ (Q *ᵥ v) i) ↔ ∃ w, v = P *ᵥ w) → ∃ (Tn : Matrix (Fin d) (Fin d) (WCb l)) (R : Matrix (Fin d) (Fin d') (WCb l)) (R' : Matrix (Fin d') (Fin d) (WCb l)), IsUnit Tn ∧ (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (Q - Tn * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (Q * R' - Tn) i j) := by
  intro l _ K bk d d' n Q P hn hP hS hker
  obtain ⟨S, hS⟩ := hS
  obtain ⟨U, Uinv, hU, hUi, h1, h2, hdich⟩ := GlobalTheory.T.smith_form_coefficientRing_image_or_prime_dvd_row l K bk (oe_dvr l K bk) d' P hP
  classical
  let J : Finset (Fin d') := Finset.univ.filter (fun j => ¬ ∃ w : Fin d' → WCb l, (fun i => U i j) = P *ᵥ w)
  have hi : ∀ j ∉ J, ∀ i, (l : WCb l) ^ n ∣ (Q * U) i j := by
    intro j hj i
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
    have := (hker (fun i => U i j)).mpr hj i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hii : ∀ v : Fin d' → WCb l, (∀ i, (l : WCb l) ^ n ∣ (Q *ᵥ v) i) → ∀ j ∈ J, (l : WCb l) ∣ (Uinv *ᵥ v) j := by
    intro v hv j hj
    obtain ⟨w, rfl⟩ := (hker v).mp hv
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hr := (hdich j).resolve_left hj
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.dvd_sum (fun k _ => (hr k).mul_right _)
  obtain ⟨e, hunit, hdiv⟩ := GlobalTheory.T.wittCompletedTilt_columns_of_right_inverse_mod_pow l d d' n Q S U Uinv J hn hS h1 h2 hi hii
  refine ⟨Q * U.submatrix id (fun k => (e k : Fin d')), Uinv.submatrix (fun k => (e k : Fin d')) id,
    U.submatrix id (fun k => (e k : Fin d')), hunit, fun i j => hUi _ _, fun i j => hU _ _, hdiv, ?_⟩
  intro i j
  simp [Matrix.mul_submatrix_one, Matrix.submatrix]

end GlobalTheory.SmithQuot
