module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleSemiAbelianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalCoverSymmBundlePowerDecompositStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfLbPowLbIsoLinComb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBOfPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleGenericSemiAb

theorem isAmpleLB_of_generic_of_symm (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R]
    (hc : IsAdicComplete (maximalIdeal R) R) (G : Over (Sp R)) [GrpObj G] (hG : IsSemiAbelian G)
    (hA : IsAbelianScheme ((Over.pullback (jK R)).obj G)) (L : LB G.left) (hL : L.IsLB)
    (hLK : RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))))
    (hs : LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L) : IsAmpleLB L := by
  obtain ⟨M, hMa, hMs⟩ := GlobalTheory.T.exists_ample_symmetric_lineBundle_semiAbelian R G hG hA
  have hMK : RelAmple ((Over.pullback (jK R)).obj G) (M.pull (pullback.fst G.hom (jK R))) := by
    have : IsProper ((Over.pullback (jK R)).obj G).hom := hA.proper
    have h1 : IsAffineHom (jK R) := by unfold jK; infer_instance
    have : IsAffineHom (pullback.fst G.hom (jK R)) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback G.hom (jK R)).flip h1
    exact (relAmple_iff_isAmpleLB_of_isAffine ((Over.pullback (jK R)).obj G) (LB.isLB_linComb hMa.isLB _ _)).2
      (hMa.pull_of_isAffineHom _)
  obtain ⟨R', _, _, _, _, _, ρ, G', _, π, hinj, hfin, hpb, N, a₀, r, a, β, hN, ha₀, -, hiso⟩ :=
    GlobalTheory.T.exists_finiteNormalCover_symmBundle_power_decomposition R hc G hG hA L M hL hMa.isLB hLK hMK hs hMs
  have : IsFinite π := by
    have : IsFinite (spMap ρ) := by
      unfold spMap
      rw [IsFinite.SpecMap_iff]; exact hfin
    exact MorphismProperty.of_isPullback (P := @IsFinite) hpb.1.flip this
  have hamp := GlobalTheory.AmplePowLinComb.isAmpleLB_of_lbPow_lbIso_linComb _ (L.pull π) (M.pull π)
    (hMa.pull_of_isFinite π) (LB.isLB_linComb hL _ _) N a₀ r a (fun i => (β i).left) hN ha₀ hiso
  obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R
  exact GlobalTheory.AmpleFiniteBase.isAmpleLB_of_pull R R' ρ hinj hfin G G' π hG hpb L hL hamp

theorem isAmpleLB_of_generic : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R],
    IsAdicComplete (maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
    IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ L : LB G.left, L.IsLB →
    RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) →
    LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → IsAmpleLB L :=
  fun R _ _ _ _ hc G _ hG hA L hL hLK hs => isAmpleLB_of_generic_of_symm R hc G hG hA L hL hLK hs

end GlobalTheory.AmpleGenericSemiAb
