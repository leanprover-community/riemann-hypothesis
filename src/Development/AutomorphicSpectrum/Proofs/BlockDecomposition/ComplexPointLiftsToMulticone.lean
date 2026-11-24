module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImageZMCoordIdealOfEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointHasNonzeroLift, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticone

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointHasNonzeroLift =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointHasNonzeroLift", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef\nimport Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr\n\n"}
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

theorem exists_isUnder_of_cxPt (m : ℕ) (n : Fin (m + 1) → ℕ) (y : CxPts (mpStr ℤ m n) σ₀) :
    ∃ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ IsUnder y z := by
  have hc : ∀ k, ∃ i, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := fun k =>
    ⟨ptChart _ k, CxPts.mem_ptsIn.2 (mem_ptChart _ k)⟩
  choose c hc using hc
  let z : (Σ k, Bk n k) → ℂ := fun p =>
    CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n p.1 (c p.1)) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2) y
  have hz1 : ∀ k, z ⟨k, c k⟩ = 1 := fun k => by
    change CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k)) (pullRatio (prB n k) _ (c k) le_rfl (c k)) y = 1
    rw [pullRatio_self, CxPts.ev_eq (hc k), map_one]
  refine ⟨z, fun k => ⟨c k, by rw [hz1]; exact one_ne_zero⟩, fun k i => ?_⟩
  have hmem : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) ↔ z ⟨k, i⟩ ≠ 0 := by
    have e := CxPts.mem_ptsIn_basicOpen (hc k) (pullRatio (prB n k) _ (c k) le_rfl i)
    rw [basicOpen_pullRatio, CxPts.mem_ptsIn_inf] at e
    exact ⟨fun h => e.1 ⟨hc k, h⟩, fun h => (e.2 h).2⟩
  refine ⟨hmem, fun j hi => ?_⟩
  have hW : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i) :=
    CxPts.mem_ptsIn_inf.2 ⟨hc k, hi⟩
  have r1 : ∀ l, CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i)
      (pullRatio (prB n k) _ (c k) inf_le_left l) y = z ⟨k, l⟩ := fun l => by
    rw [← resG_pullRatio (φ := prB n k) (W := blockChart n k (c k)) (i := c k) (hi := le_rfl) inf_le_left]
    exact CxPts.ev_res inf_le_left hW _
  have r2 : CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i)
      (pullRatio (prB n k) _ i inf_le_right j) y =
      CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y := by
    rw [← resG_pullRatio (φ := prB n k) (W := blockChart n k i) (i := i) (hi := le_rfl) inf_le_right]
    exact CxPts.ev_res inf_le_right hW _
  have e := congrArg (fun f => CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i) f y)
    (pullRatio_mul_pullRatio (φ := prB n k) (W := blockChart n k (c k) ⊓ blockChart n k i) (i := c k) (j := i)
      (k := j) (hi := inf_le_left) (hj := inf_le_right))
  simp only [CxPts.ev_mul, r1, r2] at e
  rw [eq_div_iff (hmem.1 hi), mul_comm]
  exact e

end GlobalTheory.CompanionTheory.MPDict
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointHasNonzeroLift =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticone =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticone", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointHasNonzeroLift\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImageZMCoordIdealOfEq\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine\nimport ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.UnderIdeal

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {A Ω : Type*} [CommRing A] [Field Ω]

theorem eval_eq_zero_of_mem_mCoordIdeal (e : A →+* Ω) (he : Function.Injective e) (ρ : (Σ k, ι k) → A)
    {f : Geo.MRing ι} (hf : f ∈ Geo.mCoordIdeal fun p => e (ρ p)) (ε : A →+* ℂ) (t : K → ℂ) :
    eval (fun p => t p.1 * ε (ρ p)) (MvPolynomial.map (Int.castRingHom ℂ) f) = 0 := by
  let q : Geo.MRing ι →+* MvPolynomial K A := eval₂Hom (Int.castRingHom _) fun p => C (ρ p) * X p.1
  have h1 : (MvPolynomial.map e).comp q =
      (Geo.mConeMap (fun p => e (ρ p)) : Geo.MRing ι →ₐ[ℤ] MvPolynomial K Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · simp [q]
    · simp [q, Geo.mConeMap]
  have h0 : q f = 0 := by
    refine map_injective e he ?_
    rw [map_zero]
    have := congrArg (fun g => g f) h1
    refine this.trans ?_
    exact hf
  have h2 : (eval₂Hom ε t).comp q =
      (eval (fun p => t p.1 * ε (ρ p))).comp (MvPolynomial.map (Int.castRingHom ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · simp [q]
    · simp [q, mul_comm]
  have := congrArg (fun g => g f) h2
  simp only [RingHom.comp_apply, h0, map_zero] at this
  exact this.symm

end Alg

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem ptCoord_eq_mul (x : MP ℤ m n) (c : ∀ k, Bk n k) (hx : x ∈ mchart c) :
    ∃ b : Fin (m + 1) → (MP ℤ m n).residueField x, (∀ k, b k ≠ 0) ∧ ∀ p : Σ k, Bk n k,
      ptCoord x p = b p.1 * (MP ℤ m n).evaluation (mchart c) x hx
        (resG _ (mchart_le c p.1) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2)) := by
  have key : ∀ k, ∃ b : (MP ℤ m n).residueField x, b ≠ 0 ∧ ∀ j : Bk n k,
      ptCoord x ⟨k, j⟩ = b * (MP ℤ m n).evaluation (blockChart n k (c k)) x (mchart_le c k hx)
        (pullRatio (prB n k) _ (c k) le_rfl j) := by
    intro k
    let W₀ := blockChart n k (ptChart x k)
    let W₁ := blockChart n k (c k)
    let V := W₀ ⊓ W₁
    have hxV : x ∈ V := ⟨mem_ptChart x k, mchart_le c k hx⟩
    have hV₀ : V ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := inf_le_left
    have hV₁ : V ≤ prB n k ⁻¹ᵁ chart ℤ (n k) (c k) := inf_le_right
    have e₀ : ∀ j : Bk n k, ptCoord x ⟨k, j⟩ =
        (MP ℤ m n).evaluation V x hxV (pullRatio (prB n k) V (ptChart x k) hV₀ j) := by
      intro j
      show (MP ℤ m n).evaluation W₀ x (mem_ptChart x k) (pullRatio (prB n k) W₀ (ptChart x k) le_rfl j) = _
      rw [← ProjImage.evaluation_resG (inf_le_left : V ≤ W₀) x hxV]
      exact congrArg _ (resG_pullRatio (φ := prB n k) (hi := le_rfl) inf_le_left)
    have e₁ : ∀ j : Bk n k, (MP ℤ m n).evaluation W₁ x (mchart_le c k hx)
        (pullRatio (prB n k) W₁ (c k) le_rfl j) =
        (MP ℤ m n).evaluation V x hxV (pullRatio (prB n k) V (c k) hV₁ j) := by
      intro j
      rw [← ProjImage.evaluation_resG (inf_le_right : V ≤ W₁) x hxV]
      exact congrArg _ (resG_pullRatio (φ := prB n k) (hi := le_rfl) inf_le_right)
    refine ⟨(MP ℤ m n).evaluation V x hxV (pullRatio (prB n k) V (ptChart x k) hV₀ (c k)), ?_, fun j => ?_⟩
    · intro h0
      have e := congrArg ((MP ℤ m n).evaluation V x hxV)
        ((pullRatio_mul_pullRatio (φ := prB n k) (hi := hV₀) (hj := hV₁) (k := ptChart x k)).trans pullRatio_self)
      rw [map_mul, h0, zero_mul, map_one] at e
      exact zero_ne_one e
    · refine (e₀ j).trans ?_
      rw [e₁ j, ← map_mul]
      exact congrArg _ (pullRatio_mul_pullRatio (φ := prB n k) (hi := hV₀) (hj := hV₁) (k := j)).symm
  choose b hb hbe using key
  refine ⟨b, hb, fun p => ?_⟩
  rw [ProjImage.evaluation_resG]
  exact hbe p.1 p.2

theorem evaluation_genericPoint_injective {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (h : genericPoint X ∈ U) :
    Function.Injective (X.evaluation U (genericPoint X) h) := by
  have h1 : Function.Injective (X.residue (genericPoint X)).hom :=
    RingHom.injective (R := X.functionField) (X.residue (genericPoint X)).hom
  exact h1.comp (fnOf_injective U h)

end GlobalTheory.CompanionTheory.MPDict.UnderIdeal

namespace GlobalTheory.CompanionTheory.MPDict


open UnderIdeal in
theorem exists_mem_mcPts_isUnder : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀), ∃ z ∈ mcPts (ptIdeal (i (genericPoint X))), IsUnder (PtsOver.map i rfl _ y) z := by
  intro m n X _ i _ y
  obtain ⟨z, hz, hu⟩ := exists_isUnder_of_cxPt m n (PtsOver.map i rfl _ y)
  refine ⟨z, ⟨hz, fun f hf => ?_⟩, hu⟩
  choose c hc using hz
  have hwk : ∀ k, PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k)) :=
    fun k => (hu k (c k)).1.2 (hc k)
  have hwV : PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) :=
    CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => CxPts.mem_ptsIn.1 (hwk k))
  have hyV : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart c) := hwV
  have hη : genericPoint X ∈ i ⁻¹ᵁ mchart c :=
    ((genericPoint_spec X).mem_open_set_iff (i ⁻¹ᵁ mchart c).isOpen).2 ⟨_, trivial, CxPts.mem_ptsIn.1 hyV⟩
  obtain ⟨b, hb, hbe⟩ := ptCoord_eq_mul (i (genericPoint X)) c hη
  let r : (Σ k, Bk n k) → Γ(MP ℤ m n, mchart c) := fun p =>
    resG _ (mchart_le c p.1) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2)
  let ρ : (Σ k, Bk n k) → Γ(X, i ⁻¹ᵁ mchart c) := fun p => (i.app (mchart c)).hom (r p)
  let φ := (i.residueFieldMap (genericPoint X)).hom
  have hf' : f ∈ Geo.mCoordIdeal fun p => (X.evaluation _ _ hη).hom (ρ p) := by
    have e := ProjImage.imageZ_mCoordIdeal_of_eq (ι := Bk n) (ι' := Bk n) id Function.injective_id id (fun _ => rfl) φ
      (fun k => φ (b k)) (fun k => (map_ne_zero φ).2 (hb k))
      (ptCoord (i (genericPoint X))) (fun p => (X.evaluation _ _ hη).hom (ρ p)) (fun p => by
        rw [hbe p, map_mul]
        congr 1
        exact Scheme.evaluation_naturality_apply _ _ _ _)
    rw [ptIdeal, ← e] at hf
    simpa [ReciprocityTheory.ChartRestriction.G.AI.I4.imageZ] using hf
  have h := eval_eq_zero_of_mem_mCoordIdeal (X.evaluation _ _ hη).hom
    (evaluation_genericPoint_injective _ hη) ρ hf' (evHom hyV) (fun k => z ⟨k, c k⟩)
  have hz' : (fun p : Σ k, Bk n k => z ⟨p.1, c p.1⟩ * evHom hyV (ρ p)) = z := by
    funext ⟨k, j⟩
    have e1 : evHom hyV (ρ ⟨k, j⟩) = z ⟨k, j⟩ / z ⟨k, c k⟩ := by
      rw [← CxPts.ev_eq hyV]
      refine Eq.trans ?_ ((hu k (c k)).2 j (hwk k))
      refine Eq.trans ?_ (CxPts.ev_res (mchart_le c k) hwV _)
      exact (valR_comp y.1 i (mchart c) (r ⟨k, j⟩)).symm
    show z ⟨k, c k⟩ * evHom hyV (ρ ⟨k, j⟩) = z ⟨k, j⟩
    rw [e1, mul_div_cancel₀ _ (hc k)]
  rw [hz'] at h
  exact h

end GlobalTheory.CompanionTheory.MPDict
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticone =====
