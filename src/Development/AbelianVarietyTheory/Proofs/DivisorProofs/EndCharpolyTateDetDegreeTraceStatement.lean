module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Mathlib.RingTheory.Flat.TorsionFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDegreePolynomialMapEqCharpolyRatioStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyEndCharpolySpecStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharpolyTateDetDegreeTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.endCharpoly_tate_det_degree_trace : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A), (∀ [Module.Finite ℚ_[l] (Vl l A)], (charpoly f).map (algebraMap ℤ ℚ_[l]) = (vmap l (A := A) (B := A) f.asHom).charpoly) ∧ (∀ [Module.Free ℤ_[l] (Tl l A)] [Module.Finite ℤ_[l] (Tl l A)], (charpoly f).map (algebraMap ℤ ℤ_[l]) = (tend l A f).charpoly) ∧ LinearMap.det (vmap l (A := A) (B := A) f.asHom) = (deg (A := A) (B := A) f.asHom : ℚ_[l]) ∧ LinearMap.trace ℚ_[l] _ (vmap l (A := A) (B := A) f.asHom) = (trace f : ℚ_[l]) := by
  intro K _ l _ hl A f
  have hcharpoly [Module.Finite ℚ_[l] (Vl l A)] (g : End A) :
      (charpoly g).map (algebraMap ℤ ℚ_[l]) = (vmap l g.asHom).charpoly := by
    obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A g
    have h := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate
      K l hl A g ((charpoly g).map (algebraMap ℤ ℚ)) (hm.map _)
      (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hd])
      (fun n => by simpa using congrArg (algebraMap ℤ ℚ) (hev n))
    rw [← h, Polynomial.map_map, show (algebraMap ℚ ℚ_[l]).comp (algebraMap ℤ ℚ) =
      algebraMap ℤ ℚ_[l] from Subsingleton.elim _ _]
  refine ⟨fun {_} => hcharpoly f, fun {_ _} => ?_, ?_, ?_⟩
  · apply Polynomial.map_injective (algebraMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
    rw [Polynomial.map_map, ← LinearMap.charpoly_baseChange,
      show (algebraMap ℤ_[l] ℚ_[l]).comp (algebraMap ℤ ℤ_[l]) =
        algebraMap ℤ ℚ_[l] from Subsingleton.elim _ _]
    exact hcharpoly f
  · obtain ⟨-, -, -, hfin, hrk⟩ := tl_free_finrank K l hl A
    have hneg : vmap l f.asHom = (-1 : ℚ_[l]) • vmap l (-f).asHom := by
      simp [vmap, LinearMap.baseChange_neg]
    have hev : (charpoly (-f)).eval 0 = (deg f.asHom : ℤ) := by
      simpa using (GlobalTheory.T.abelianVarietyEndCharpoly_spec K A (-f)).1.2.2 0
    rw [hneg, LinearMap.det_smul, LinearMap.det_eq_sign_charpoly_coeff, ← hcharpoly (-f),
      Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, hev, hrk, pow_mul, neg_one_sq, one_pow]
    simp
  · obtain ⟨-, -, -, hfin, -⟩ := tl_free_finrank K l hl A
    rw [linTrace_eq_neg_nextCoeff, ← hcharpoly f,
      Polynomial.nextCoeff_map (RingHom.injective_int (algebraMap ℤ ℚ_[l])), trace]
    simp
