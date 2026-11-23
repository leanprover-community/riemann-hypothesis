module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFieldPullbackAppTopBijectiveAndTriv
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.SeesawReduced

theorem triv_locally_of_dense : ∀ (R : Type) [CommRing R] [IsReduced R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → Smooth f → IsProper f → GeometricallyIntegral f → IsProjBy f → Dense {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧ IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)} → ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsUnit (g r) → Triv (M.pull π) := by
  intro R _ _ X f M hM hSm hPr hGI hPB hD p
  haveI := hPr
  haveI := hGI

  have hP : Nonempty (Perf f M) := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R X f hSm hPB M hM
  have hQ : Nonempty (Perf f (pw M (-1))) := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R X f hSm hPB _ (isLB_pw hM (-1))

  have hC := GlobalTheory.TrivLocus.isClosed_trivLocus R X f M hM hP hQ hPr hGI
  have hAll := hD.closure_eq.symm.trans hC.closure_eq
  have hmem : ∀ q : PrimeSpectrum R, q ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K)
      (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
      IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)} := by
    intro q; rw [← hAll]; exact Set.mem_univ q

  obtain ⟨K, _, g, X₁, π₁, f₁, hk, hpb, htr⟩ := hmem p
  obtain ⟨K₀, _, g₀, X₀, π₀, f₀, hk₀, hpb₀, hbij, htr₀⟩ :=
    GlobalTheory.GeomFibre.exists_field_pullback_appTop_bijective_and_triv R X f M hM hPr hGI K g X₁ π₁ f₁ hpb htr
  obtain ⟨r, I, hr, -, hI⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R X f M hM hP inferInstance inferInstance
    K₀ g₀ X₀ π₀ f₀ hpb₀ hbij htr₀
  refine ⟨r, ?_, ?_⟩
  · intro hrp
    apply hr
    have hrk : r ∈ RingHom.ker g₀ := by rw [hk₀, hk]; exact hrp
    exact RingHom.mem_ker.1 hrk

  have hvan : ∀ x ∈ I, x * r = 0 := by
    intro x hx
    apply IsReduced.eq_zero
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    intro J hJ
    let q : PrimeSpectrum R := ⟨J, hJ⟩
    by_cases hrJ : r ∈ J
    · exact J.mul_mem_left x hrJ
    · apply J.mul_mem_right r
      obtain ⟨L, _, gq, Xq, πq, fq, hkq, hpbq, htrq⟩ := hmem q
      have hu : IsUnit (gq r) := by
        rw [isUnit_iff_ne_zero]
        intro h0
        have hrk : r ∈ RingHom.ker gq := RingHom.mem_ker.2 h0
        rw [hkq] at hrk
        exact hrJ hrk
      have := ((hI L gq Xq πq fq hpbq hu).1 htrq) hx
      rw [RingHom.mem_ker] at this
      show x ∈ q.asIdeal
      rw [← hkq]; exact this
  intro R' _ g' X' π f' hpb' hu'
  refine (hI R' g' X' π f' hpb' hu').2 ?_
  intro x hx
  rw [RingHom.mem_ker]
  have h0 : g' x * g' r = 0 := by rw [← map_mul, hvan x hx, map_zero]
  exact (hu'.mul_left_eq_zero).1 h0

end GlobalTheory.SeesawReduced
