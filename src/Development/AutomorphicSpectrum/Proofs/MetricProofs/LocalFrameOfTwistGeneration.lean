module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoeffsRegularInChart
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

theorem frames_at_point : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {E : Type} [AddCommGroup E]
    [Module Ω E] {κ : Type} (x : κ → Ω) (L : GlobalTheory.CompanionTheory.Ar.Lat ξ E) (m n r : ℕ) (V : Submodule Ω E)
    (φ : Fin n → Module.Dual Ω E) (cc : Fin r → E) (hV : L.IsVB r V) (hli : LinearIndependent Ω cc)
    (hsp : Submodule.span Ω (Set.range cc) = V) (hG : IsTwistGen ξ x L m φ) (P : Cpt ξ) (c₁ : κ)
    (hc : InChart ξ x c₁ P),
    ∃ (T : Matrix (Fin r) (Fin r) Ω) (C : Matrix (Fin n) (Fin r) Ω) (B : Matrix (Fin r) (Fin n) Ω),
      T.det ≠ 0 ∧ Matrix.of (fun j a => φ j (cc a)) * T = (x c₁ ^ m) • C ∧ B * C = 1 ∧
        (∀ j a, C j a ∈ regAt ξ P) ∧ ∀ a j, B a j ∈ regAt ξ P := by
  intro X Ω _ ξ E _ _ κ x L m n r V φ cc hV hli hsp hG P c₁ hc
  obtain ⟨U, hPU, b, hbV, hfr⟩ := (show L.IsVBOn Set.univ r V from hV) P (Set.mem_univ _)
  have hbP : L.IsFrameAt b P := hfr P (Set.mem_univ _) hPU
  obtain ⟨B, hBreg, hCreg, hBC⟩ :=
    GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse X Ω ξ E κ x L m n r φ hG P c₁ hc b hbP
  have hmem : ∀ a, ∃ t : Fin r → Ω, ∑ l, t l • cc l = b a := by
    intro a
    have hba : b a ∈ Submodule.span Ω (Set.range cc) := by
      rw [hsp, ← hbV]
      exact Submodule.subset_span ⟨a, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 hba
  choose t ht using hmem
  refine ⟨Matrix.of fun l a => t a l, Matrix.of (fun j a => φ j (b a) / x c₁ ^ m), B, ?_, ?_, hBC, ?_, hBreg⟩
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hli_b := hbP.1
    rw [Fintype.linearIndependent_iff] at hli_b
    have hcol : ∀ l, ∑ a, t a l * v a = 0 := fun l => by
      simpa [Matrix.mulVec, dotProduct] using congrFun hv l
    have hsum : ∑ a, v a • b a = 0 := by
      calc ∑ a, v a • b a = ∑ a, v a • ∑ l, t a l • cc l := by simp only [ht]
        _ = ∑ l, (∑ a, t a l * v a) • cc l := by
          simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]
        _ = 0 := by simp [hcol]
    exact hv0 (funext fun a => hli_b v hsum a)
  · ext j a
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 : ∑ l, φ j (cc l) * t a l = φ j (b a) := by

      rw [← ht a, map_sum]
      simp only [map_smul, smul_eq_mul]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [h1]
    by_cases hx : x c₁ ^ m = 0
    · exfalso
      have h2 := congrFun (congrFun hBC a) a
      simp [Matrix.mul_apply, hx, Matrix.one_apply] at h2
    · field_simp
  · intro j a
    exact hCreg j a

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
