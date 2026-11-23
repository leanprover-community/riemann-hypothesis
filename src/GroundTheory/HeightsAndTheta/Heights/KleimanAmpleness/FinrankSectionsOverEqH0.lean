module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideExtra
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreFurther
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraSide
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestExtra
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver cechHc cechZc cechBc quotPart GlobalSectionsComparisonStatement)

noncomputable section

theorem altSum_eq_of_vanish (f : ℕ → ℕ) (B : ℕ) (h : ∀ i, 1 ≤ i → f i = 0) :
    ∑ i ∈ Finset.range (B + 1), (-1 : ℚ) ^ i * (f i : ℚ) = f 0 := by
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun i _ => by rw [h (i + 1) (by omega)]; simp]
  simp

theorem finrank_sectionsOver_eq_H0 (hB : GlobalSectionsComparisonStatement) {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K]
    {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (n : K → ℤ) :
    Module.finrank F (secOver F y n) = Module.finrank F (cechHc ι (quotPart F (mIdealOver F y)) n 0) := by
  obtain ⟨φ, hinj, hrange, -⟩ := hB F K ι Ω y n hy
  let e1 : ↥(cechZc ι (quotPart F (mIdealOver F y)) n 0) ≃ₗ[F] secOver F y n :=
    (LinearEquiv.ofInjective φ hinj).trans (LinearEquiv.ofEq _ _ hrange)
  have hbot : (cechBc ι (quotPart F (mIdealOver F y)) n 0).comap
      (cechZc ι (quotPart F (mIdealOver F y)) n 0).subtype = ⊥ := by
    rw [cechBc, Submodule.comap_bot, Submodule.ker_subtype]
  let e2 : cechHc ι (quotPart F (mIdealOver F y)) n 0 ≃ₗ[F] ↥(cechZc ι (quotPart F (mIdealOver F y)) n 0) :=
    Submodule.quotEquivOfEqBot _ hbot
  rw [← e1.finrank_eq, e2.finrank_eq]

theorem SectionsPoly.proof (hB : GlobalSectionsComparisonStatement) (hE : EulerPoly.Statement) (hM : MultiSerre.Statement)
    (hR : RayVanish.Statement) : SectionsPoly.Statement := by
  intro F _ K _ dK ι _ Ω _ _ y k₀ hmod
  let lo : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  obtain rfl : dK = @LinearOrder.toDecidableEq K lo := Subsingleton.elim _ _
  have hV : NumbersDVR.IsMultiHomogIdeal (mIdealOver F y) := isMultiHomogIdeal_mIdealOver y
  obtain ⟨B, χ, -, -, hχ⟩ := hE F K ι (mIdealOver F y) hV
  have key : ∀ m : K → ℤ, (∀ i : ℕ, 1 ≤ i → Subsingleton (cechHc ι (quotPart F (mIdealOver F y)) m i)) →
      (Module.finrank F (secOver F y m) : ℚ) = eval (fun k => (m k : ℚ)) χ := by
    intro m hm
    rw [← hχ m, finrank_sectionsOver_eq_H0 hB y hmod.1 m]
    refine (altSum_eq_of_vanish (fun i => Module.finrank F (cechHc ι (quotPart F (mIdealOver F y)) m i)) B
      fun i hi => ?_).symm
    have := hm i hi
    exact Module.finrank_zero_of_subsingleton
  refine ⟨χ, ?_, fun β => ?_⟩
  · filter_upwards [hM F K ι (mIdealOver F y) hV] with m hm
    rw [← hm.2, ← key m hm.1, finrank_sectionsOver_eq_H0 hB y hmod.1 m]
    push_cast
    rfl
  · filter_upwards [hR F K ι Ω y k₀ hmod β] with c hc
    exact key _ hc

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
