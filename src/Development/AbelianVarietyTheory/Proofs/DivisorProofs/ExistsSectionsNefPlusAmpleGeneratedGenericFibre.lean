module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingSecsOfClsEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExtendingRationalGenericFibreMulIntStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefRationalFibreOfNefFiniteFieldFibresStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefFibreTwistExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreeEqOrderSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfIsNef
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.GenFibreGen

theorem nefFib_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (n : ℕ), NefFib L → NefFib (L.pow n) := by
  intro k _ X _ p D hX L n hL
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have htriv : NefFib (HermLB.triv p) := by
      intro Z i _ _ κ _ _ _ _
      exact (interNum_eq_zero_of_cls_eq_zero κ _
        (fun _ => LB.isLB_pull (LB.isLB_triv X) i) 0
        (by rw [CechPic.cls_pull (LB.isLB_triv X)]; exact map_zero _)).ge
    refine AmpleTwistNef.nefFib_of_cls_eq ?_ htriv
    erw [CechPic.cls_lbPow L.isLB 0, zero_smul]
    rfl
  · have := hX.finite
    exact (nefFib_pow_iff k X p hX.isProjOver L n hn).2 hL

theorem exists_fst_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (x : X), CharZero (X.residueField x) → ∃ y : ↥(Limits.pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))), Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) y = x :=
  fun k _ X p x hx => RatDegZeros.mem_range_fst k X p x hx

theorem isProjOver_snd {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) : IsProjOver (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) := by
  have := h.finite
  have := h.isIntegral
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 h.finite
  obtain ⟨_, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 h.isProjOver
  have hP : IsProjOver (p ≫ spMap (Int.castRingHom k)) := hL.isProjOver _
  exact ProjSpace.isProjOver_pullback_snd (Int.castRingHom ℚ) hP

theorem exists_secs_generic : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), NefFib L → IsAmpleLB A.B → ∃ (m : ℕ) (N : ℕ) (s : Fin N → (((L.pow n).tens A).pow m).B.Sec), 1 ≤ m ∧ ∀ x : X, CharZero (X.residueField x) → ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i) := by
  intro hNN k _ X _ p D hX L A n hL hA
  have hN := GlobalTheory.T.isNef_rationalFibre_of_nef_finiteFieldFibres k X p D hX (L.pow n) (nefFib_pow k X p D hX L n hL)
  have : IsAffineHom (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have hA' : IsAmpleLB (A.B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))) :=
    hA.pull_of_isAffineHom _
  have hK := IsAmpleLB.tens_of_isNef hNN ℚ _ _ (isProjOver_snd hX) _ _ hA' hN
  obtain ⟨m, hm, N, t, ht⟩ := hK.exists_isGenerated_pow
  have hM := pull_isLB (((L.pow n).tens A).pow m).isLB (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
  obtain ⟨v, hv⟩ := CechPic.exists_generating_secs_of_cls_eq _ _ _ (isLB_lbPow hK.isLB m) hM (by
      rw [CechPic.cls_lbPow hK.isLB m, CechPic.cls_pull (((L.pow n).tens A).pow m).isLB _ hM]
      erw [CechPic.cls_lbPow ((L.pow n).tens A).isLB m]
      rw [map_nsmul]
      congr 1
      erw [CechPic.cls_tens (pull_isLB A.isLB _) (pull_isLB (L.pow n).isLB _), CechPic.cls_tens (L.pow n).isLB A.isLB]
      rw [map_add (f := _), CechPic.cls_pull A.isLB, CechPic.cls_pull (L.pow n).isLB, add_comm]) (Fin N) t ht
  choose s hs using fun i => GlobalTheory.T.exists_section_extending_rationalGenericFibre_mul_int k X p D hX _ (((L.pow n).tens A).pow m).isLB (v i)
  refine ⟨m, N, s, hm, fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := exists_fst_eq k X p x hx
  have hy : y ∈ ⨆ i, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (v i) := hv ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  exact ⟨i, (hs i y).2 hi⟩

end GlobalTheory.GenFibreGen
