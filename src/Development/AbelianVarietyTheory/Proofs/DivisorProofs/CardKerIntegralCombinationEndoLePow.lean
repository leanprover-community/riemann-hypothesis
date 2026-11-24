module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLeOfPullbackLePowFiniteEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBoundRingActionPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionFiniteEtaleAbelianVarietyCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OEndDegree

theorem card_ker_le : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (d : ℕ) (a : Fin d → 𝓞 E), ∃ C : ℕ, ∀ (n : Fin d → ℤ) (K : ℕ), (∀ i, (n i).natAbs ≤ K) → ∑ i, n i • a i ≠ 0 → Finite {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1} ∧ Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act (∑ i, n i • a i) = 1} ≤ C * K ^ (2 * g) := by
  intro E _ _ k _ _ _ A _ act g hB hg d a
  haveI := hB.comm
  haveI : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  obtain ⟨H, m, s, c, hH, hs, hc, hsec⟩ := GlobalTheory.T.exists_veryAmple_bound_ringAction_pullback E k A act g hB hg d a
  obtain ⟨C, hC⟩ := GlobalTheory.T.degree_le_of_pullback_le_pow_finiteEtale k A.left A.hom g hg H m s hH hs
  refine ⟨C * c ^ g, fun n K hn hb => ?_⟩
  have hK : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with rfl | h
    · exfalso; apply hb
      refine Finset.sum_eq_zero fun i _ => ?_
      have := hn i
      rw [Nat.le_zero, Int.natAbs_eq_zero] at this
      rw [this, zero_smul]
    · exact h
  obtain ⟨hfin, het, hker⟩ := GlobalTheory.T.ringAction_finite_etale_abelianVariety_charZero E k A act g hB hg _ hb
  refine ⟨hker, ?_⟩
  have hrank := GlobalTheory.finrank_eq_card_kernel_points_of_etale k A hB (act.act (∑ i, n i • a i))
  have hφ : (act.act (∑ i, n i • a i)).left ≫ A.hom = A.hom := Over.w _
  have hq : 1 ≤ c * K ^ 2 := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
  have h := hC (act.act (∑ i, n i • a i)).left hφ _ (c * K ^ 2) hq hrank (hsec n K hK hn)
  calc _ ≤ C * (c * K ^ 2) ^ g := h
    _ = C * c ^ g * K ^ (2 * g) := by ring

end GlobalTheory.OEndDegree
