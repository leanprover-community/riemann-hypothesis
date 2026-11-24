module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimension
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimensionStatement, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureDimIffArithmeticVariety, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealHorizontalIffCharZero, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionary

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimensionStatement =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimensionStatement", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimension\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef\nimport Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

theorem _root_.GlobalTheory.T.arithmetic_variety_point_dimension : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ), CharZero ((MP ℤ m n).residueField x) → topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) → Geo.IsArithVar (ptIdeal x) d := by
  exact @GlobalTheory.CompanionTheory.MPDict.DimVar.isArithVar_ptIdeal
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimensionStatement =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureDimIffArithmeticVariety =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureDimIffArithmeticVariety", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine\nimport Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimensionStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.QuasiAffine\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.KrullDimension.Polynomial\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef\nimport Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.DimClosure

private theorem exists_ringKrullDim_le_add_of_finiteType {R A : Type*} [CommRing R] [CommRing A]
    [IsNoetherianRing R] (f : R →+* A) (hf : f.FiniteType) :
    ∃ N : ℕ, ringKrullDim A ≤ ringKrullDim R + N := by
  letI := f.toAlgebra
  obtain ⟨k, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hf
  refine ⟨k, ?_⟩
  calc ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin k) R) :=
        ringKrullDim_le_of_surjective g.toRingHom hg
    _ = ringKrullDim R + k := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem exists_open_nhd_topologicalKrullDim_MP_le {m : ℕ} {n : Fin (m + 1) → ℕ} (y : MP ℤ m n) :
    ∃ U : (MP ℤ m n).Opens, y ∈ U ∧ ∃ N : ℕ, topologicalKrullDim (U : Set (MP ℤ m n)) ≤ N := by
  haveI : AlgebraicGeometry.IsProper (mpStr ℤ m n) := isProper_mpStr ℤ m n
  obtain ⟨U, hU, hyU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (U := (⊤ : (MP ℤ m n).Opens)) (x := y) (by simp)
  refine ⟨U, hyU, ?_⟩
  have hZ := AlgebraicGeometry.isAffineOpen_top (Spec (CommRingCat.of ℤ))
  have hft := AlgebraicGeometry.Scheme.Hom.finiteType_appLE (mpStr ℤ m n) hZ hU
    (by simp)
  haveI : IsNoetherianRing ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) :=
    isNoetherianRing_of_ringEquiv ℤ (Scheme.ΓSpecIso (CommRingCat.of ℤ)).symm.commRingCatIsoToRingEquiv
  obtain ⟨N, hN⟩ := exists_ringKrullDim_le_add_of_finiteType _ hft
  have hZdim : ringKrullDim ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv]
    have h1 := Ring.krullDimLE_iff.mp (IsPrincipalIdealRing.krullDimLE_one ℤ)
    exact_mod_cast h1
  haveI := hU.isOpenImmersion_fromSpec
  have htop : topologicalKrullDim (U : Set (MP ℤ m n)) =
      ringKrullDim ((MP ℤ m n).presheaf.obj (Opposite.op U)) := by
    rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  refine ⟨N + 1, ?_⟩
  rw [htop]
  calc ringKrullDim ((MP ℤ m n).presheaf.obj (Opposite.op U))
        ≤ ringKrullDim ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) + N := hN
    _ ≤ 1 + N := by gcongr
    _ = ((N + 1 : ℕ) : WithBot ℕ∞) := by push_cast; exact add_comm _ _

private theorem exists_topologicalKrullDim_MP_le {m : ℕ} {n : Fin (m + 1) → ℕ} :
    ∃ d : ℕ, topologicalKrullDim (MP ℤ m n) ≤ d := by
  haveI : AlgebraicGeometry.IsProper (mpStr ℤ m n) := isProper_mpStr ℤ m n
  haveI : CompactSpace (MP ℤ m n) :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace (mpStr ℤ m n)
  choose U hyU N hN using fun y : MP ℤ m n => exists_open_nhd_topologicalKrullDim_MP_le y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (U y : Set (MP ℤ m n)))
    (fun y => (U y).isOpen) (fun y _ => Set.mem_iUnion.mpr ⟨y, hyU y⟩)
  refine ⟨t.sup N, GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen fun z => ?_⟩
  obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z))
  refine ⟨U y, (U y).isOpen, hzy, (hN y).trans ?_⟩
  exact_mod_cast Finset.le_sup (f := N) hy

theorem exists_dim_closure_eq {m : ℕ} {n : Fin (m + 1) → ℕ} (x : MP ℤ m n) :
    ∃ e : ℕ, topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (e : ℕ) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_MP_le (m := m) (n := n)
  have hle : topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) ≤ d :=
    (topologicalKrullDim_subspace_le _ _).trans hd
  have hnn : 0 ≤ topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) := by
    haveI : Nonempty (IrreducibleCloseds (closure ({x} : Set (MP ℤ m n)))) :=
      ⟨⟨closure {(⟨x, subset_closure (Set.mem_singleton x)⟩ : closure ({x} : Set (MP ℤ m n)))},
        isIrreducible_singleton.closure, isClosed_closure⟩⟩
    unfold topologicalKrullDim
    exact Order.krullDim_nonneg
  generalize topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = D at hle hnn ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hnn (not_le.mpr (WithBot.bot_lt_coe _))
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h5 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞) := hle
      exact ENat.natCast_ne_top d (top_le_iff.mp (WithBot.coe_le_coe.mp h5))
    | coe e => exact ⟨e, rfl⟩

theorem dim_closure_iff_isArithVar : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ),
    CharZero ((MP ℤ m n).residueField x) →
      (topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) ↔ Geo.IsArithVar (ptIdeal x) d) := by
  intro m n x d hc
  refine ⟨GlobalTheory.T.arithmetic_variety_point_dimension m n x d hc, fun h => ?_⟩
  obtain ⟨e, he⟩ := exists_dim_closure_eq x
  have h' := GlobalTheory.T.arithmetic_variety_point_dimension m n x e hc he
  have h1 := h.2.2.2
  have h2 := h'.2.2.2
  have hde : d = e := by
    have h3 := h1.symm.trans h2
    have h4 : d + Fintype.card (Fin (m + 1)) = e + Fintype.card (Fin (m + 1)) := by exact_mod_cast h3
    omega
  rw [he, hde]

end GlobalTheory.CompanionTheory.MPDict.DimClosure
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureDimIffArithmeticVariety =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealHorizontalIffCharZero =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealHorizontalIffCharZero", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef\nimport Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

private theorem C_mem_ptIdeal_iff_intCast_residueField_eq_zero (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (c : ℤ) :
    (MvPolynomial.C c : Geo.MRing (Bk n)) ∈ ptIdeal x ↔ ((c : ℤ) : (MP ℤ m n).residueField x) = 0 := by
  rw [ptIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, MvPolynomial.aeval_C, eq_intCast,
    ← map_intCast (MvPolynomial.C : (MP ℤ m n).residueField x →+* MvPolynomial (Fin (m + 1)) ((MP ℤ m n).residueField x)) c,
    MvPolynomial.C_eq_zero]

theorem ptIdeal_isHorizontal_iff (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) :
    Geo.IsHorizontal (ptIdeal x) ↔ CharZero ((MP ℤ m n).residueField x) := by
  constructor
  · intro h
    have h' : (ptIdeal x).comap (MvPolynomial.C : ℤ →+* Geo.MRing (Bk n)) = ⊥ := h
    refine charZero_of_inj_zero fun k hk => ?_
    have hm : ((k : ℤ)) ∈ (ptIdeal x).comap (MvPolynomial.C : ℤ →+* Geo.MRing (Bk n)) := by
      rw [Ideal.mem_comap, C_mem_ptIdeal_iff_intCast_residueField_eq_zero]
      exact_mod_cast hk
    rw [h', Ideal.mem_bot] at hm
    exact_mod_cast hm
  · intro h
    show (ptIdeal x).comap (MvPolynomial.C : ℤ →+* Geo.MRing (Bk n)) = ⊥
    rw [eq_bot_iff]
    intro c hc
    rw [Ideal.mem_bot]
    rw [Ideal.mem_comap, C_mem_ptIdeal_iff_intCast_residueField_eq_zero] at hc
    exact Int.cast_eq_zero.mp hc

end GlobalTheory.CompanionTheory.MPDict
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealHorizontalIffCharZero =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionary =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionary", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureDimIffArithmeticVariety\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealHorizontalIffCharZero\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsHorizontal charOf)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ.PtDictProof

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem C_mem_ptIdeal_iff (x : MP ℤ m n) (a : ℤ) :
    (C a : MRing (Bk n)) ∈ ptIdeal x ↔ (a : (MP ℤ m n).residueField x) = 0 := by
  rw [ptIdeal, ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal, RingHom.mem_ker, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap,
    MvPolynomial.aeval_C]
  have h : (algebraMap ℤ (MvPolynomial (Fin (m + 1)) ((MP ℤ m n).residueField x)) a) =
      MvPolynomial.C (a : (MP ℤ m n).residueField x) := by
    simp
  rw [h, MvPolynomial.C_eq_zero]

theorem evaluation_generic_injective (Z : Scheme.{0}) [IsIntegral Z] :
    Function.Injective (Z.evaluation ⊤ (genericPoint Z) (Opens.mem_top _)).hom := by
  rw [← Scheme.germ_residue, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Injective.comp ?_ (germ_injective_of_isIntegral Z _ _)
  exact RingHom.injective (Z.residue (genericPoint Z)).hom

theorem dim_closure_image_generic {X Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ X) [IsClosedImmersion j] :
    topologicalKrullDim (closure ({j (genericPoint Z)} : Set X)) = topologicalKrullDim Z := by
  have hg := (genericPoint_spec Z).image (f := j) j.isClosedEmbedding.continuous
  have hcl : closure ({j (genericPoint Z)} : Set X) = Set.range j := by
    have h1 : closure ({j (genericPoint Z)} : Set X) = closure (j '' Set.univ) := hg
    rw [h1, Set.image_univ]
    exact j.isClosedEmbedding.isClosed_range.closure_eq
  rw [hcl]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    j.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

theorem charZero_residueField_iff {Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ MP ℤ m n) :
    CharZero ((MP ℤ m n).residueField (j (genericPoint Z))) ↔ CharZero Γ(Z, ⊤) := by
  constructor
  · intro h
    haveI : CharZero (Z.residueField (genericPoint Z)) :=
      charZero_of_injective_ringHom (f := (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom)
        (RingHom.injective _)
    exact RingHom.charZero (Z.evaluation ⊤ (genericPoint Z) (Opens.mem_top _)).hom
  · intro h
    haveI : CharZero (Z.residueField (genericPoint Z)) :=
      charZero_of_injective_ringHom (evaluation_generic_injective Z)
    exact RingHom.charZero (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom

theorem charOf_prime {P : Ideal (MRing (Bk n))} [P.IsPrime] (h : ¬ IsHorizontal P) : (charOf P).Prime := by
  unfold charOf
  rw [← Int.prime_iff_natAbs_prime]
  exact Submodule.IsPrincipal.prime_generator_of_isPrime _ h

theorem C_charOf_mem (P : Ideal (MRing (Bk n))) : (C ((charOf P : ℕ) : ℤ) : MRing (Bk n)) ∈ P := by
  have hg := Submodule.IsPrincipal.generator_mem (P.comap (C : ℤ →+* MRing (Bk n)))
  obtain ⟨c, hc⟩ := Int.dvd_natAbs.mpr
    (dvd_refl (Submodule.IsPrincipal.generator (P.comap (C : ℤ →+* MRing (Bk n)))))
  have hmem : ((charOf P : ℕ) : ℤ) ∈ P.comap (C : ℤ →+* MRing (Bk n)) := by
    unfold charOf
    rw [hc]
    exact Ideal.mul_mem_right c _ hg
  exact Ideal.mem_comap.mp hmem

theorem charOf_cast_eq_zero {Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ MP ℤ m n) :
    ((charOf (ptIdeal (j (genericPoint Z))) : ℕ) : Γ(Z, ⊤)) = 0 := by
  have h1 := (C_mem_ptIdeal_iff (j (genericPoint Z)) _).mp (C_charOf_mem _)
  have h2 := congrArg (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom h1
  apply evaluation_generic_injective Z
  rw [map_natCast, map_zero]
  simpa using h2

end GlobalTheory.CompanionTheory.MixZ.PtDictProof

namespace GlobalTheory.CompanionTheory.MixZ


open GlobalTheory.CompanionTheory.MixZ.PtDictProof in
theorem ptDict : PtDict := by
  intro m n Z _ j _ d hd
  have hP := isMultiProjPrime_ptIdeal m n (j (genericPoint Z))
  haveI : (ptIdeal (j (genericPoint Z))).IsPrime := hP.1
  have hH : IsHorizontal (ptIdeal (j (genericPoint Z))) ↔ CharZero Γ(Z, ⊤) :=
    (ptIdeal_isHorizontal_iff m n _).trans (charZero_residueField_iff j)
  refine ⟨hP, hH, fun h => ?_, fun h => ⟨charOf_prime h, charOf_cast_eq_zero j⟩⟩
  have hc : CharZero ((MP ℤ m n).residueField (j (genericPoint Z))) :=
    (ptIdeal_isHorizontal_iff m n _).mp h
  have hdim : topologicalKrullDim (closure ({j (genericPoint Z)} : Set (MP ℤ m n))) = (d : ℕ) := by
    rw [dim_closure_image_generic j, hd]
  exact (_root_.GlobalTheory.CompanionTheory.MPDict.DimClosure.dim_closure_iff_isArithVar m n _ d hc).mp hdim

end GlobalTheory.CompanionTheory.MixZ
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionary =====
