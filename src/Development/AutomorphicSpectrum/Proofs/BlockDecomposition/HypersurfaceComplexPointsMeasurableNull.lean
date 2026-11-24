module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticone
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DehomogenizedEvalEqRatio
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedFormNonzeroOnGenericPoint
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroLocusRegularFunctionNull
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

@[expose] public section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ

section ZeroLocus

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {X : Scheme.{0}} [IsIntegral X] {i : X ⟶ MP ℤ m n}

theorem mem_ptsIn_preimage_mchart (c : ∀ k, Bk n k) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) ↔
      PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := by
  rw [CxPts.mem_ptsIn, CxPts.mem_ptsIn]
  rfl

theorem ev_dehomog_eq_zero_iff (c : ∀ k, Bk n k) {f : Pol n} {a : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a)
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (hy : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c))
    {z : (Σ k, Bk n k) → ℂ} (hz : IsUnder (PtsOver.map i rfl _ y) z) :
    ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) (i.app _ (dehomog c f)) y = 0 ↔
      eval z (map (Int.castRingHom ℂ) f) = 0 := by
  have hw := (mem_ptsIn_preimage_mchart c y).1 hy
  have hne : ∏ k, z ⟨k, c k⟩ ^ a k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ =>
    pow_ne_zero _ ((hz k (c k)).1.1 (CxPts.ptsIn_mono (mchart_le c k) hw))
  rw [CxPts.ev_app i rfl, _root_.GlobalTheory.CompanionTheory.MixZ.ev_dehomog_of_isUnder m n c f a hf _ z hz hw, div_eq_zero_iff]
  exact ⟨fun h => h.resolve_right hne, Or.inl⟩

theorem zeroLocus_eq_iUnion [IsClosedImmersion i] {f : Pol n} {a : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a) :
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀ | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧
      eval z (map (Int.castRingHom ℂ) f) = 0} =
    ⋃ c : ∀ k, Bk n k, {y | y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) ∧
      ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) (i.app _ (dehomog c f)) y = 0} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨z, hz, h0⟩
    have hc : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀
        (i ⁻¹ᵁ mchart fun k => ptChart ((PtsOver.map i rfl _ y).1 (IsLocalRing.closedPoint ℂ)) k) :=
      (mem_ptsIn_preimage_mchart _ y).2 (CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => mem_ptChart _ k))
    exact ⟨_, hc, (ev_dehomog_eq_zero_iff _ hf y hc hz).2 h0⟩
  · rintro ⟨c, hc, h0⟩
    obtain ⟨z, -, hz⟩ := _root_.GlobalTheory.CompanionTheory.MPDict.exists_mem_mcPts_isUnder m n X i y
    exact ⟨z, hz, (ev_dehomog_eq_zero_iff c hf y hc hz).1 h0⟩

theorem measurableSet_ev_eq_zero {Y : Scheme.{0}} (q : Y ⟶ Sp ℤ) (W : Y.Opens) (g : Γ(Y, W)) :
    MeasurableSet {y : GlobalTheory.CxPts q σ₀ | y ∈ ptsIn q σ₀ W ∧ ev q σ₀ W g y = 0} := by
  have hS : IsOpen (ptsIn q σ₀ W) := isOpen_ptsIn W
  have hO : IsOpen (ptsIn q σ₀ W ∩ ev q σ₀ W g ⁻¹' {0}ᶜ) :=
    (continuousOn_ev g).isOpen_inter_preimage hS isOpen_compl_singleton
  have e : {y : GlobalTheory.CxPts q σ₀ | y ∈ ptsIn q σ₀ W ∧ ev q σ₀ W g y = 0} =
      ptsIn q σ₀ W \ (ptsIn q σ₀ W ∩ ev q σ₀ W g ⁻¹' {0}ᶜ) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff, not_and, not_not]
    exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
  rw [e]
  exact hS.measurableSet.diff hO.measurableSet

end ZeroLocus

theorem zeroLocus_measurable_null : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a → f ∉ ptIdeal (i (genericPoint X)) →
    MeasurableSet {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀ | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧
      eval z (map (Int.castRingHom ℂ) f) = 0} ∧
    ∀ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, volume (c.e.target ∩ c.e.symm ⁻¹'
      {y | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧ eval z (map (Int.castRingHom ℂ) f) = 0}) = 0 := by
  intro m n X _ i _ D f a hf hI
  rw [zeroLocus_eq_iUnion hf]
  refine ⟨MeasurableSet.iUnion fun c => measurableSet_ev_eq_zero _ _ _, fun ch => ?_⟩
  rw [Set.preimage_iUnion, Set.inter_iUnion]
  refine measure_iUnion_null fun c => ?_
  by_cases hg : genericPoint X ∈ i ⁻¹ᵁ mchart c
  · exact _root_.GlobalTheory.CompanionTheory.MixZ.volume_chart_zeroSet_fnOf X (i ≫ mpStr ℤ m n) σ₀ D ch _ hg _ (_root_.GlobalTheory.CompanionTheory.MixZ.FnForm.fnAt_ne_zero_of_notMem_ptIdeal m n X i c hg f a hf hI)
  · have e : ch.e.target ∩ ch.e.symm ⁻¹' {y | y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) ∧
        ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) (i.app _ (dehomog c f)) y = 0} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun v hv => hg
        (((genericPoint_spec X).mem_open_set_iff (i ⁻¹ᵁ mchart c).isOpen).2
          ⟨_, trivial, CxPts.mem_ptsIn.1 hv.2.1⟩)
    rw [e, measure_empty]

end GlobalTheory.CompanionTheory.MixZ
