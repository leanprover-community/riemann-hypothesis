module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.A3oneOfFactSplitOfCountCont, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorPower

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.A3oneOfFactSplitOfCountCont =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.A3oneOfFactSplitOfCountCont", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Vanishing
open GlobalTheory.ShFam.BdArc (IsHolPts)

namespace GlobalTheory.CuspDim.IsoPow

variable {Z : Scheme.{0}} {B : LB Z}

theorem res_res {U V W : Z.Opens} (h : V ≤ U) (h' : W ≤ V) (u : Γ(Z, U)ˣ) :
    res h' (res h u) = res (h'.trans h) u := by
  ext
  change (Z.presheaf.map (homOfLE h).op ≫ Z.presheaf.map (homOfLE h').op).hom u.val = _
  rw [← Functor.map_comp]
  rfl

theorem pow_le (n : ℕ) (j : PUnit → B.ι) : (lbPow B n).U j ≤ B.U (j PUnit.unit) :=
  LB.wchart_le B (fun _ => 𝟙 Z) j PUnit.unit

theorem res_pow_g (n : ℕ) (j j' : PUnit → B.ι) {W : Z.Opens} (h : W ≤ (lbPow B n).U j ⊓ (lbPow B n).U j') :
    res h ((lbPow B n).g j j') =
      res (h.trans (inf_le_inf (pow_le n j) (pow_le n j'))) (B.g (j PUnit.unit) (j' PUnit.unit)) ^ n := by
  have e : (lbPow B n).g j j' =
      res (inf_le_inf (pow_le n j) (pow_le n j')) (B.g (j PUnit.unit) (j' PUnit.unit)) ^ (n : ℤ) :=
    Fintype.prod_unique fun a : PUnit.{1} => res (le_inf (inf_le_left.trans (LB.wchart_le B (fun _ => 𝟙 Z) j a))
      (inf_le_right.trans (LB.wchart_le B (fun _ => 𝟙 Z) j' a))) (pullU (𝟙 Z) _ (B.g (j a) (j' a))) ^ (n : ℤ)
  rw [e, zpow_natCast, map_pow, _root_.ReciprocityTheory.ChartRestriction.G.DVR.res_res']



theorem ev_res_pow {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} {U W : Z.Opens} {y : CxPts q σ} (h : W ≤ U)
    (hy : y ∈ ptsIn q σ W) (u : Γ(Z, U)ˣ) (n : ℕ) :
    ev q σ W (res h u ^ n).val y = ev q σ U u.val y ^ (n : ℤ) := by
  rw [zpow_natCast, ← ev_res h hy, ev_eq hy, ev_eq hy, Units.val_pow_eq_pow_val, map_pow]
  rfl

end GlobalTheory.CuspDim.IsoPow
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.A3oneOfFactSplitOfCountCont =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorPower =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorPower", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.A3oneOfFactSplitOfCountCont\npublic import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef\nimport Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr\n\n"}
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

namespace GlobalTheory.CompanionTheory.MPDict.PowRep

open GlobalTheory.CuspDim.IsoPow
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet (powLine powLine_a constLine)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem h_powLine {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : Geo.HermLine ι) (r : ℕ)
    (z : (Σ k, ι k) → ℂ) : (powLine A r).h z = A.h z ^ r := by
  induction r with
  | zero => simp [powLine, constLine]
  | succ r ih => simp [powLine, Geo.HermLine.tensor, ih, pow_succ]

theorem frame_pow {Z : Scheme.{0}} (B : LB Z) (r : ℕ) (V : Z.Opens) (u : ∀ i, Γ(Z, B.U i ⊓ V)ˣ)
    (h : ∀ i j, Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          B.U i ⊓ B.U j ⊓ V ≤ B.U j ⊓ V) (u j) =
        Semi.res (inf_le_left : B.U i ⊓ B.U j ⊓ V ≤ B.U i ⊓ B.U j) (B.g i j) *
          Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            B.U i ⊓ B.U j ⊓ V ≤ B.U i ⊓ V) (u i))
    (j j' : PUnit.{1} → B.ι) :
    Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        (lbPow B r).U j ⊓ (lbPow B r).U j' ⊓ V ≤ (lbPow B r).U j' ⊓ V)
        (Semi.res (inf_le_inf_right V (pow_le r j')) (u (j' PUnit.unit)) ^ r) =
      Semi.res (inf_le_left : (lbPow B r).U j ⊓ (lbPow B r).U j' ⊓ V ≤ (lbPow B r).U j ⊓ (lbPow B r).U j')
          ((lbPow B r).g j j') *
        Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          (lbPow B r).U j ⊓ (lbPow B r).U j' ⊓ V ≤ (lbPow B r).U j ⊓ V)
          (Semi.res (inf_le_inf_right V (pow_le r j)) (u (j PUnit.unit)) ^ r) := by
  have hW : (lbPow B r).U j ⊓ (lbPow B r).U j' ⊓ V ≤
      B.U (j PUnit.unit) ⊓ B.U (j' PUnit.unit) ⊓ V :=
    inf_le_inf_right V (inf_le_inf (pow_le r j) (pow_le r j'))
  have e := congrArg (fun t => Semi.res hW t ^ r) (h (j PUnit.unit) (j' PUnit.unit))
  simp only [map_mul, mul_pow, GlobalTheory.CuspDim.IsoPow.res_res] at e
  rw [res_pow_g]
  simp only [map_pow, GlobalTheory.CuspDim.IsoPow.res_res]
  exact e

theorem res_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W W' : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (h' : W' ≤ W) :
    Semi.res h' (blockUnit i j h) = blockUnit i j (h'.trans h) :=
  GlobalTheory.CuspDim.IsoPow.res_res _ _ _

theorem ev_res_pow {p : (MP ℤ m n) ⟶ Sp ℤ} {W U : (MP ℤ m n).Opens} (h : W ≤ U) (v : Γ(MP ℤ m n, U)ˣ) (r : ℕ)
    {y : CxPts p σ₀} (hy : y ∈ ptsIn p σ₀ W) :
    CxPts.ev p σ₀ W ((Semi.res h v ^ r : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) y =
      CxPts.ev p σ₀ U (v : Γ(MP ℤ m n, U)) y ^ r := by
  rw [Units.val_pow_eq_pow_val, CxPts.ev_eq hy, map_pow, ← CxPts.ev_eq hy]
  exact congrArg (· ^ r) (CxPts.ev_res h hy _)

theorem chart_pow {B : LB (MP ℤ m n)} (A : Geo.HermLine (Bk n)) (r : ℕ) (j : PUnit.{1} → B.ι) (c c' : ∀ k, Bk n k)
    (v : Γ(MP ℤ m n, B.U (j PUnit.unit) ⊓ mchart c)ˣ) (v' : Γ(MP ℤ m n, B.U (j PUnit.unit) ⊓ mchart c')ˣ)
    (h : Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          B.U (j PUnit.unit) ⊓ (mchart c ⊓ mchart c') ≤ B.U (j PUnit.unit) ⊓ mchart c) v =
        Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          B.U (j PUnit.unit) ⊓ (mchart c ⊓ mchart c') ≤ B.U (j PUnit.unit) ⊓ mchart c') v' *
        ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
          ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
            B.U (j PUnit.unit) ⊓ (mchart c ⊓ mchart c') ≤
              prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ A.a k) :
    Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
        (lbPow B r).U j ⊓ (mchart c ⊓ mchart c') ≤ (lbPow B r).U j ⊓ mchart c)
        (Semi.res (inf_le_inf_right _ (pow_le r j)) v ^ r) =
      Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
        (lbPow B r).U j ⊓ (mchart c ⊓ mchart c') ≤ (lbPow B r).U j ⊓ mchart c')
        (Semi.res (inf_le_inf_right _ (pow_le r j)) v' ^ r) *
      ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
        ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
          (lbPow B r).U j ⊓ (mchart c ⊓ mchart c') ≤
            prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ (powLine A r).a k := by
  have hW : (lbPow B r).U j ⊓ (mchart c ⊓ mchart c') ≤ B.U (j PUnit.unit) ⊓ (mchart c ⊓ mchart c') :=
    inf_le_inf_right _ (pow_le r j)
  have e := congrArg (fun t => Semi.res hW t ^ r) h
  simp only [map_mul, mul_pow, map_prod, map_zpow, GlobalTheory.CuspDim.IsoPow.res_res] at e
  simp only [map_pow, GlobalTheory.CuspDim.IsoPow.res_res]
  refine e.trans (congrArg _ ?_)
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [powLine_a, mul_comm, zpow_mul, zpow_natCast]
  exact congrArg (fun t => (t ^ A.a k) ^ r) (res_blockUnit _ _ _ _)

theorem isHermRep_pow (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)) (r : ℕ)
    (hM : IsHermRep M A) : IsHermRep (M.pow r) (powLine A r) := by
  obtain ⟨u, h₁, h₂, h₃⟩ := hM
  refine ⟨fun (j : PUnit.{1} → M.B.ι) c =>
    Semi.res (inf_le_inf_right _ (pow_le (B := M.B) r j)) (u (j PUnit.unit) c) ^ r, ?_, ?_, ?_⟩
  · intro j j' c
    exact frame_pow M.B r (mchart c) (fun i => u i c) (fun i j => h₁ i j c) j j'
  · intro j c c'
    exact chart_pow A r j c c' _ _ (h₂ (j PUnit.unit) c c')
  · intro (j : PUnit.{1} → M.B.ι) c y z hz hy
    have hy' : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U (j PUnit.unit) ⊓ mchart c) :=
      CxPts.ptsIn_mono (inf_le_inf_right _ (pow_le (B := M.B) r j)) hy
    have e := h₃ (j PUnit.unit) c y z hz hy'
    have eφ : ((M.pow r).φ σ₀).φ j y = r * (M.φ σ₀).φ (j PUnit.unit) y := by
      exact ((M.φ σ₀).zpow_φ r j y).trans (by simp)
    have ev := ev_res_pow (p := mpStr ℤ m n) (inf_le_inf_right (mchart c) (pow_le (B := M.B) r j))
      (u (j PUnit.unit) c) r hy
    beta_reduce
    rw [h_powLine, e, eφ, show CxPts.ev (mpStr ℤ m n) σ₀ ((M.pow r).B.U j ⊓ mchart c) _ y = _ from ev, norm_pow, mul_pow, mul_pow, ← Finset.prod_pow,
      ← Real.exp_nat_mul, mul_div_assoc]
    congr 2
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [powLine_a, mul_comm, zpow_mul, zpow_natCast]

end GlobalTheory.CompanionTheory.MPDict.PowRep
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorPower =====
