module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KernelTrivialOfEveryPointCovered
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKernelTrivialOfOpenCover
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KTrivJacobson

theorem exists_specializes {R : Type} [CommRing R] {J : Ideal R} (hJ : J ≤ Ideal.jacobson ⊥)
    (p : PrimeSpectrum R) :
    ∃ q : PrimeSpectrum (R ⧸ J), p ⤳ PrimeSpectrum.comap (Ideal.Quotient.mk J) q := by
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top
  have hJm : J ≤ m := hJ.trans (sInf_le ⟨bot_le, hm⟩)
  have : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hJm
  obtain ⟨q, hq⟩ := this
  refine ⟨q, ?_⟩
  rw [hq, ← PrimeSpectrum.le_iff_specializes]
  exact hpm

theorem kTriv_of_quotient : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (J : Ideal R), J ≤ Ideal.jacobson ⊥ → ∀ (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → ∀ M : LB B.left, M.IsLB → RelAmple B M → ∀ (Y₀ : Over (Spec (CommRingCat.of (R ⧸ J)))) [GrpObj Y₀] (b : Y₀.left ⟶ B.left), IsGrpPullback Y₀ B (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) b → ∀ N₀ : LB Y₀.left, N₀.IsLB → LBIso N₀ (M.pull b) → KTriv Y₀ N₀ → KTriv B M := by
  intro R _ _ J hJ B _ hB M hM hA Y₀ _ b hb N₀ hN₀ e hK
  have key : ∀ p : Spec (CommRingCat.of R), ∃ U : (Spec (CommRingCat.of R)).Opens, p ∈ U ∧
      KTriv ((Over.pullback U.ι).obj B) (M.pull (pullback.fst B.hom U.ι)) := fun p => by
    obtain ⟨q, hq⟩ := exists_specializes hJ p
    obtain ⟨U, hU, H⟩ := GlobalTheory.KTrivGlob.exists_open hM hN₀ hB hA hb e hK q
    exact ⟨U, hq.mem_open U.2 hU, H⟩
  choose U hU hK using key
  have hL := fun p => LB.isLB_pull hM (pullback.fst B.hom (U p).ι)
  exact GlobalTheory.CoverGlue.kTriv_of_cover _ _ U B _ _
    (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hU p⟩)
    (fun p => isGrpPullback_pullback B (U p).ι) _ _ hM hL (fun p => GlobalTheory.lbIso_refl (hL p)) hB
    (fun p => GlobalTheory.isAbelianScheme_pullback_obj (U p).ι B hB) hK

end GlobalTheory.KTrivJacobson
