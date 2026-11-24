module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueComplexPointUnder
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIsUnder, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdZpowSingle, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullRatioTopEq, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvProdBlockUnit

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIsUnder =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIsUnder", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueComplexPointUnder\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef\nimport Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.UnderExists

theorem exists_isUnder : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (z : (Σ k, Bk n k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ y : CxPts (mpStr ℤ m n) σ₀, IsUnder y z :=
  fun m n z hz => (GlobalTheory.CompanionTheory.MPDict.Under.existsUnique_isUnder m n z hz).exists

end GlobalTheory.CompanionTheory.MPDict.UnderExists
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIsUnder =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdZpowSingle =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdZpowSingle", "h": "module\n\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.TypeStar\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.TwUnits

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (h'' : W ≤ U) (x : Γ(X, U)ˣ) :
    Semi.res h' (Semi.res h x) = Semi.res h'' x := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom x.val) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_div_g {X : Scheme.{0}} (T L : LB X) (p q : T.ι × L.ι) {W : X.Opens}
    (h : W ≤ (T.U p.1 ⊓ L.U p.2) ⊓ (T.U q.1 ⊓ L.U q.2)) (h₁ : W ≤ T.U p.1 ⊓ T.U q.1) (h₂ : W ≤ L.U p.2 ⊓ L.U q.2) :
    Semi.res h ((LB.div T L).g p q) = Semi.res h₁ (T.g p.1 q.1) * (Semi.res h₂ (L.g p.2 q.2))⁻¹ :=
  (map_mul (Semi.res h) _ _).trans (congrArg₂ (· * ·) (res_res' _ _ h₁ _)
    ((map_inv (Semi.res h) _).trans (congrArg (·⁻¹) (res_res' _ _ h₂ _))))

theorem iso_law {X : Scheme.{0}} {L T : LB X} {w : LB.Iso L T} (hw : w.IsGen) (p q : T.ι × L.ι) {W : X.Opens}
    (hp : W ≤ T.U p.1 ⊓ L.U p.2) (hq : W ≤ T.U q.1 ⊓ L.U q.2) (h₁ : W ≤ T.U p.1 ⊓ T.U q.1)
    (h₂ : W ≤ L.U p.2 ⊓ L.U q.2) :
    Semi.res hp (w.s p) = Semi.res h₁ (T.g p.1 q.1) * (Semi.res h₂ (L.g p.2 q.2))⁻¹ * Semi.res hq (w.s q) := by
  have e := congrArg (Semi.res (le_inf hp hq)) (hw p q)
  exact ((res_res' _ _ hp _).symm.trans e).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (res_div_g T L p q (le_inf hp hq) h₁ h₂) (res_res' _ _ hq _)))

theorem res_pull_g (k : Fin (m + 1)) (j j' : PUnit → Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ ((O1 ℤ (n k)).pull (pr ℤ m n k)).U j ⊓ ((O1 ℤ (n k)).pull (pr ℤ m n k)).U j')
    (h' : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (j PUnit.unit) ⊓ chart ℤ (n k) (j' PUnit.unit))) :
    Semi.res h (((O1 ℤ (n k)).pull (pr ℤ m n k)).g j j') = blockUnit (j PUnit.unit) (j' PUnit.unit) h' := by
  have e := linComb_punit_g (O1 ℤ (n k)) (pr ℤ m n k) 1 j j'
  rw [zpow_one] at e
  exact (congrArg (Semi.res h) e).trans (res_res' _ _ h' _)

def twIdx (b : Fin m) (t : ℤ) (c : ∀ k, Bk n k) : (twB m n b t).ι :=
  Prod.mk (fun _ => c b.succ) (fun _ => c 0)

theorem mchart_le_U (b : Fin m) (t : ℤ) (c : ∀ k, Bk n k) : mchart c ≤ (twB m n b t).U (twIdx b t c) :=
  fun _ hx => ⟨Set.mem_iInter.2 fun _ => mchart_le c _ hx, Set.mem_iInter.2 fun _ => mchart_le c _ hx⟩

theorem blk_le {c c' : ∀ k, Bk n k} {W : (MP ℤ m n).Opens} (hW : W ≤ mchart c ⊓ mchart c') (k : Fin (m + 1)) :
    W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)) :=
  fun _ hx => ⟨mchart_le c k (hW hx).1, mchart_le c' k (hW hx).2⟩

theorem res_twB_g (b : Fin m) (t : ℤ) (c c' : ∀ k, Bk n k) {W : (MP ℤ m n).Opens} (hW : W ≤ mchart c ⊓ mchart c')
    (h : W ≤ (twB m n b t).U (twIdx b t c) ⊓ (twB m n b t).U (twIdx b t c')) :
    Semi.res h ((twB m n b t).g (twIdx b t c) (twIdx b t c')) =
      blockUnit (c b.succ) (c' b.succ) (blk_le hW b.succ) * blockUnit (c 0) (c' 0) (blk_le hW 0) ^ t := by
  have h₁ : W ≤ ((O1 ℤ (n b.succ)).pull (pr ℤ m n b.succ)).U (fun _ => c b.succ) ⊓
      ((O1 ℤ (n b.succ)).pull (pr ℤ m n b.succ)).U (fun _ => c' b.succ) :=
    le_inf (fun _ hx => h hx |>.1.1) (fun _ hx => h hx |>.2.1)
  have h₂ : W ≤ ((O1 ℤ (n 0)).pull (pr ℤ m n 0)).U (fun _ => c 0) ⊓
      ((O1 ℤ (n 0)).pull (pr ℤ m n 0)).U (fun _ => c' 0) :=
    le_inf (fun _ hx => h hx |>.1.2) (fun _ hx => h hx |>.2.2)
  have e₁ := res_pull_g b.succ (fun _ => c b.succ) (fun _ => c' b.succ) h₁ (blk_le hW b.succ)
  have e₂ := res_pull_g 0 (fun _ => c 0) (fun _ => c' 0) h₂ (blk_le hW 0)
  have e₃ : (Semi.res h₂ (((O1 ℤ (n 0)).pull (pr ℤ m n 0)).g (fun _ => c 0) (fun _ => c' 0)) ^ (-t))⁻¹ =
      blockUnit (c 0) (c' 0) (blk_le hW 0) ^ t := by
    rw [zpow_neg, inv_inv]
    exact congrArg (· ^ t) e₂
  exact (res_div_g _ _ (twIdx b t c) (twIdx b t c') h h₁ h₂).trans (congrArg₂ (· * ·) e₁
    ((congrArg (·⁻¹) (map_zpow (Semi.res h₂) _ (-t))).trans e₃))

theorem blockUnit_self {k : Fin (m + 1)} (i : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) i)) : blockUnit i i h = 1 := by
  rw [blockUnit, ratioUnit_self, map_one, map_one]

theorem prod_zpow_single {G : Type*} [CommGroup G] (f : Fin (m + 1) → G) (p q : Fin (m + 1)) (t : ℤ) :
    ∏ k, f k ^ ((Pi.single p 1 + t • Pi.single q 1 : Fin (m + 1) → ℤ) k) = f p * f q ^ t := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zpow_add, Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_eq_single p (fun k _ hk => by simp [hk]) (by simp)]
    simp
  · rw [Finset.prod_eq_single q (fun k _ hk => by simp [hk]) (by simp)]
    simp

variable {B : LB (MP ℤ m n)} {b : Fin m} {t : ℤ}

def uOf (w : LB.Iso B (twB m n b t)) (i : B.ι) (c : ∀ k, Bk n k) : Γ(MP ℤ m n, B.U i ⊓ mchart c)ˣ :=
  Semi.res (le_inf (inf_le_right.trans (mchart_le_U b t c)) inf_le_left) (w.s (twIdx b t c, i))

theorem res_uOf (w : LB.Iso B (twB m n b t)) (i : B.ι) (c : ∀ k, Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ B.U i ⊓ mchart c) (h' : W ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U i) :
    Semi.res h (uOf w i c) = Semi.res h' (w.s (twIdx b t c, i)) :=
  res_res' _ _ h' _

theorem frame_uOf {w : LB.Iso B (twB m n b t)} (hw : w.IsGen) (i j : B.ι) (c : ∀ k, Bk n k) :
    Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        B.U i ⊓ B.U j ⊓ mchart c ≤ B.U j ⊓ mchart c) (uOf w j c) =
      Semi.res (inf_le_left : B.U i ⊓ B.U j ⊓ mchart c ≤ B.U i ⊓ B.U j) (B.g i j) *
        Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          B.U i ⊓ B.U j ⊓ mchart c ≤ B.U i ⊓ mchart c) (uOf w i c) := by
  have hc : B.U i ⊓ B.U j ⊓ mchart c ≤ mchart c ⊓ mchart c := le_inf inf_le_right inf_le_right
  have hU := (inf_le_right : B.U i ⊓ B.U j ⊓ mchart c ≤ mchart c).trans (mchart_le_U b t c)
  have hi : B.U i ⊓ B.U j ⊓ mchart c ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U i :=
    le_inf hU (inf_le_left.trans inf_le_left)
  have hj : B.U i ⊓ B.U j ⊓ mchart c ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U j :=
    le_inf hU (inf_le_left.trans inf_le_right)
  have e := iso_law hw (twIdx b t c, i) (twIdx b t c, j) hi hj (le_inf hU hU) inf_le_left
  rw [res_twB_g b t c c hc, blockUnit_self, blockUnit_self, one_zpow, one_mul, one_mul] at e
  rw [res_uOf w j c _ hj, res_uOf w i c _ hi]
  exact (eq_inv_mul_iff_mul_eq.1 e).symm

theorem mono_uOf (hB : B.IsLB) {w : LB.Iso B (twB m n b t)} (hw : w.IsGen) (i : B.ι) (c c' : ∀ k, Bk n k) :
    Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
        B.U i ⊓ (mchart c ⊓ mchart c') ≤ B.U i ⊓ mchart c) (uOf w i c) =
      Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
        B.U i ⊓ (mchart c ⊓ mchart c') ≤ B.U i ⊓ mchart c') (uOf w i c') *
      ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
        ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
          B.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^
        (Pi.single b.succ 1 + t • Pi.single 0 1 : Fin (m + 1) → ℤ) k := by
  have hc : B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c ⊓ mchart c' := inf_le_right
  have hU := (inf_le_right.trans inf_le_left : B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c).trans (mchart_le_U b t c)
  have hU' := (inf_le_right.trans inf_le_right : B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c').trans (mchart_le_U b t c')
  have hs : Semi.res (le_inf inf_le_left inf_le_left : B.U i ⊓ (mchart c ⊓ mchart c') ≤ B.U i ⊓ B.U i) (B.g i i) = 1 :=
    Units.ext (LB.resG_g_self hB i _)
  have hi : B.U i ⊓ (mchart c ⊓ mchart c') ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U i := le_inf hU inf_le_left
  have hi' : B.U i ⊓ (mchart c ⊓ mchart c') ≤ (twB m n b t).U (twIdx b t c') ⊓ B.U i := le_inf hU' inf_le_left
  have e := iso_law hw (twIdx b t c, i) (twIdx b t c', i) hi hi' (le_inf hU hU') (le_inf inf_le_left inf_le_left)
  rw [res_twB_g b t c c' hc] at e
  change _ = _ * (Semi.res _ (B.g i i))⁻¹ * _ at e
  rw [hs, inv_one, mul_one] at e
  rw [res_uOf w i c _ hi, res_uOf w i c' _ hi',
    prod_zpow_single (fun k => blockUnit (c k) (c' k) (blk_le hc k)) b.succ 0 t]
  exact e.trans (mul_comm _ _)

theorem exists_units : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (B : LB (MP ℤ m n)) (c : Fin m) (t : ℤ), B.IsLB → LBIso B (twB m n c t) →
  ∃ u : ∀ (i : B.ι) (c' : ∀ k, Bk n k), Γ(MP ℤ m n, B.U i ⊓ mchart c')ˣ,
    (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          B.U i ⊓ B.U j ⊓ mchart c' ≤ B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : B.U i ⊓ B.U j ⊓ mchart c' ≤ B.U i ⊓ B.U j) (B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            B.U i ⊓ B.U j ⊓ mchart c' ≤ B.U i ⊓ mchart c') (u i c')) ∧
    (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ (Pi.single c.succ 1 + t • Pi.single 0 1 : Fin (m + 1) → ℤ) k) := by
  rintro m n B c t hB ⟨w, hw⟩
  exact ⟨uOf w, frame_uOf hw, mono_uOf hB hw⟩

end GlobalTheory.CompanionTheory.MPDict.TwUnits
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdZpowSingle =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullRatioTopEq =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullRatioTopEq", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef\nimport Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Unique

theorem pullRatio_top_eq {N : ℕ} {x x' : Sp ℂ ⟶ PSpace ℤ N} (i j : Fin (N + 1))
    (h : ⊤ ≤ x ⁻¹ᵁ chart ℤ N i) (h' : ⊤ ≤ x' ⁻¹ᵁ chart ℤ N i)
    (e : valR x (chart ℤ N i) (ratio ℤ N i j) = valR x' (chart ℤ N i) (ratio ℤ N i j)) :
    pullRatio x ⊤ i h j = pullRatio x' ⊤ i h' j := by
  rw [valR, valR, dite_eq_left h, dite_eq_left h'] at e
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 e

theorem valR_comp_prB {m : ℕ} {n : Fin (m + 1) → ℕ} (x : Sp ℂ ⟶ MP ℤ m n) {k : Fin (m + 1)} (i j : Bk n k)
    (h : ⊤ ≤ x ⁻¹ᵁ blockChart n k i) :
    valR (x ≫ prB n k) (chart ℤ (n k) i) (ratio ℤ (n k) i j) =
      valR x (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) := by
  have h' : ⊤ ≤ (x ≫ prB n k) ⁻¹ᵁ chart ℤ (n k) i := h
  rw [valR, valR, dite_eq_left h, dite_eq_left h', pullRatio,
    ← Scheme.Hom.appLE_comp_appLE x (prB n k) (chart ℤ (n k) i) (blockChart n k i) ⊤ le_rfl h]
  rfl

end GlobalTheory.CompanionTheory.MPDict.Unique


open GlobalTheory.CompanionTheory.MPDict.Unique in
theorem GlobalTheory.CompanionTheory.MPDict.isUnder_unique : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (z : (Σ k, Bk n k) → ℂ)
    (y y' : CxPts (mpStr ℤ m n) σ₀), IsUnder y z → IsUnder y' z → y = y' := by
  intro m n z y y' h h'
  refine Subtype.ext (GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k => ?_)
  have hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (ptChart (y.1 (IsLocalRing.closedPoint ℂ)) k)) :=
    mem_ptsIn.2 (mem_ptChart _ k)
  obtain ⟨i, hi⟩ : ∃ i, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ⟨_, hy⟩
  have hz : z ⟨k, i⟩ ≠ 0 := ((h k i).1).1 hi
  have hi' : y' ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ((h' k i).1).2 hz
  refine GlobalTheory.ProjSpace.hom_ext ?_ fun t => ⟨⊤, trivial, i, hi, hi', fun j => ?_⟩
  · have s : pr ℤ m n k ≫ PSpace.str ℤ (n k) = mpStr ℤ m n := pr_toSpecBase ℤ m n k
    rw [Category.assoc, Category.assoc, s, y.2, y'.2]
  · have a : ⊤ ≤ y.1 ⁻¹ᵁ blockChart n k i := hi
    have a' : ⊤ ≤ y'.1 ⁻¹ᵁ blockChart n k i := hi'
    refine pullRatio_top_eq (x := y.1 ≫ prB n k) (x' := y'.1 ≫ prB n k) i j a a' ?_
    rw [valR_comp_prB y.1 i j a, valR_comp_prB y'.1 i j a']
    exact ((h k i).2 j hi).trans ((h' k i).2 j hi').symm
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullRatioTopEq =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvProdBlockUnit =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvProdBlockUnit", "h": "module\n\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIsUnder\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdZpowSingle\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullRatioTopEq\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.MPDict.HermRep

section Main
variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem ev_resU {U W : (MP ℤ m n).Opens} (e : W ≤ U) {y : CxPts (mpStr ℤ m n) σ₀}
    (h : y ∈ ptsIn (mpStr ℤ m n) σ₀ W) (u : Γ(MP ℤ m n, U)ˣ) :
    CxPts.ev (mpStr ℤ m n) σ₀ W ((res e u : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) y =
      CxPts.ev (mpStr ℤ m n) σ₀ U (u : Γ(MP ℤ m n, U)) y :=
  CxPts.ev_res e h _

theorem ev_prod_zpow {W : (MP ℤ m n).Opens} {y : CxPts (mpStr ℤ m n) σ₀}
    (h : y ∈ ptsIn (mpStr ℤ m n) σ₀ W) {ι : Type} [Fintype ι] (b : ι → Γ(MP ℤ m n, W)ˣ) (e : ι → ℤ) :
    CxPts.ev (mpStr ℤ m n) σ₀ W ((∏ k, b k ^ e k : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) y =
      ∏ k, (CxPts.ev (mpStr ℤ m n) σ₀ W (b k : Γ(MP ℤ m n, W)) y) ^ e k := by
  have key : ∀ x : Γ(MP ℤ m n, W)ˣ, CxPts.ev (mpStr ℤ m n) σ₀ W (x : Γ(MP ℤ m n, W)) y =
      ((Units.map (evHom h).toMonoidHom x : ℂˣ) : ℂ) := fun x => ev_eq h _
  rw [key, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, Units.val_zpow_eq_zpow_val, key]

theorem ev_blockUnit {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hy : IsUnder y z)
    (k : Fin (m + 1)) (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (hW : y ∈ ptsIn (mpStr ℤ m n) σ₀ W) :
    CxPts.ev (mpStr ℤ m n) σ₀ W (blockUnit i j h : Γ(MP ℤ m n, W)) y = z ⟨k, j⟩ / z ⟨k, i⟩ := by
  have hi : W ≤ blockChart n k i := h.trans ((prB n k).preimage_mono inf_le_left)
  have e1 : (blockUnit i j h : Γ(MP ℤ m n, W)) = pullRatio (prB n k) W i hi j :=
    appLE_ratioOn (φ := prB n k) (i := i) (j := j)
      (inf_le_left : chart ℤ (n k) i ⊓ chart ℤ (n k) j ≤ chart ℤ (n k) i) h
  rw [e1, ← resG_pullRatio (W := blockChart n k i) (hi := le_rfl) hi, CxPts.ev_res hi hW]
  exact (hy k i).2 j (ptsIn_mono hi hW)

theorem ev_prod_blockUnit {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hy : IsUnder y z)
    (c c' : ∀ k, Bk n k) {W : (MP ℤ m n).Opens}
    (h : ∀ k, W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)))
    (hW : y ∈ ptsIn (mpStr ℤ m n) σ₀ W) (a : Fin (m + 1) → ℤ) :
    CxPts.ev (mpStr ℤ m n) σ₀ W ((∏ k, blockUnit (c k) (c' k) (h k) ^ a k : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) y =
      ∏ k, (z ⟨k, c' k⟩ / z ⟨k, c k⟩) ^ a k := by
  rw [ev_prod_zpow hW]
  exact Finset.prod_congr rfl fun k _ => by rw [ev_blockUnit hy k _ _ (h k) hW]

theorem isUnder_smul {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hy : IsUnder y z)
    (l : Fin (m + 1) → ℂ) (hl : ∀ k, l k ≠ 0) : IsUnder y (fun p => l p.1 * z p) := by
  intro k i
  obtain ⟨h1, h2⟩ := hy k i
  refine ⟨h1.trans ⟨fun h => mul_ne_zero (hl k) h, fun h => right_ne_zero_of_mul h⟩, fun j hj => ?_⟩
  rw [h2 j hj, mul_div_mul_left _ _ (hl k)]

theorem isUnder_of_smul {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (l : Fin (m + 1) → ℂ)
    (hl : ∀ k, l k ≠ 0) (hy : IsUnder y (fun p => l p.1 * z p)) : IsUnder y z := by
  have := isUnder_smul hy (fun k => (l k)⁻¹) fun k => inv_ne_zero (hl k)
  simpa only [inv_mul_cancel_left₀ (hl _)] using this

variable (M : HermLB (mpStr ℤ m n)) (a : Fin (m + 1) → ℤ)
  (u : ∀ (i : M.B.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, M.B.U i ⊓ mchart c)ˣ)

def hval (y : CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ) (i : M.B.ι) (c : ∀ k, Bk n k) : ℝ :=
  (∏ k, ‖z ⟨k, c k⟩‖ ^ a k) *
    ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖ *
      Real.exp ((M.φ σ₀).φ i y / 2)

theorem hval_chart (h1 : (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ mchart c') (u i c'))) {y : CxPts (mpStr ℤ m n) σ₀} (z : (Σ k, Bk n k) → ℂ)
    (i j : M.B.ι) (c : ∀ k, Bk n k) (hi : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c))
    (hj : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U j ⊓ mchart c)) :
    hval M a u y z i c = hval M a u y z j c := by
  rw [mem_ptsIn_inf] at hi hj
  have hij : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ M.B.U j ⊓ mchart c) :=
    mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨hi.1, hj.1⟩, hi.2⟩
  have e := congrArg (fun w : Γ(MP ℤ m n, M.B.U i ⊓ M.B.U j ⊓ mchart c)ˣ =>
    CxPts.ev (mpStr ℤ m n) σ₀ _ w.val y) (h1 i j c)
  simp only [Units.val_mul, ev_mul, ev_resU _ hij] at e
  have hg : gv (mpStr ℤ m n) σ₀ M.B i j y ≠ 0 := gv_ne_zero hi.1 hj.1
  have hpos : 0 < ‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ := norm_pos_iff.2 hg
  have ht := (M.φ σ₀).trans i j y hi.1 hj.1
  unfold hval
  rw [e, ht, norm_mul]
  change _ = _ * (‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ * _) * _
  have ex : Real.exp (((M.φ σ₀).φ i y - Real.log (‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ ^ 2)) / 2) =
      Real.exp ((M.φ σ₀).φ i y / 2) / ‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ := by
    rw [Real.log_pow, sub_div, Real.exp_sub]
    congr 1
    rw [show ((2 : ℕ) : ℝ) * Real.log ‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ / 2 =
      Real.log ‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ by push_cast; ring, Real.exp_log hpos]
  rw [ex]
  field_simp

theorem hval_multi (h2 : (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ a k)) {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ}
    (hy : IsUnder y z) (i : M.B.ι) (c c' : ∀ k, Bk n k)
    (hc : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c))
    (hc' : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c')) :
    hval M a u y z i c = hval M a u y z i c' := by
  rw [mem_ptsIn_inf] at hc hc'
  have hcc : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ (mchart c ⊓ mchart c')) :=
    mem_ptsIn_inf.2 ⟨hc.1, mem_ptsIn_inf.2 ⟨hc.2, hc'.2⟩⟩
  have e := congrArg (fun w : Γ(MP ℤ m n, M.B.U i ⊓ (mchart c ⊓ mchart c'))ˣ =>
    CxPts.ev (mpStr ℤ m n) σ₀ _ w.val y) (h2 i c c')
  simp only [Units.val_mul, ev_mul, ev_resU _ hcc] at e
  rw [ev_prod_blockUnit hy c c' (fun k => (fun _ hx => ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
    M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)))) hcc a] at e
  have hz : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k => ((hy k (c k)).1).1 (ptsIn_mono (mchart_le c k) hc.2)
  unfold hval
  rw [e, norm_mul, norm_prod]
  have hk : ∀ k, ‖z ⟨k, c k⟩‖ ^ a k * ‖(z ⟨k, c' k⟩ / z ⟨k, c k⟩) ^ a k‖ = ‖z ⟨k, c' k⟩‖ ^ a k := by
    intro k
    rw [norm_zpow, norm_div, div_zpow, mul_div_cancel₀ _ (zpow_ne_zero _ (norm_ne_zero_iff.2 (hz k)))]
  calc (∏ k, ‖z ⟨k, c k⟩‖ ^ a k) * (‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c') (u i c' : Γ(MP ℤ m n, M.B.U i ⊓ mchart c')) y‖ * ∏ k, ‖(z ⟨k, c' k⟩ / z ⟨k, c k⟩) ^ a k‖) * Real.exp ((M.φ σ₀).φ i y / 2)
      = (∏ k, (‖z ⟨k, c k⟩‖ ^ a k * ‖(z ⟨k, c' k⟩ / z ⟨k, c k⟩) ^ a k‖)) * ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c') (u i c' : Γ(MP ℤ m n, M.B.U i ⊓ mchart c')) y‖ * Real.exp ((M.φ σ₀).φ i y / 2) := by
        rw [Finset.prod_mul_distrib]; ring
    _ = _ := by simp only [hk]

end Main

section Metric
variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def ptC (y : CxPts (mpStr ℤ m n) σ₀) : ∀ k, Bk n k := fun k => ptChart (y.1 (IsLocalRing.closedPoint ℂ)) k

theorem mem_ptC (y : CxPts (mpStr ℤ m n) σ₀) : y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart (ptC y)) :=
  mem_ptsIn.2 (Set.mem_iInter.2 fun k => mem_ptChart _ k)

variable (M : HermLB (mpStr ℤ m n)) (a : Fin (m + 1) → ℤ)
  (u : ∀ (i : M.B.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, M.B.U i ⊓ mchart c)ˣ)

theorem mem_pick_ptC (y : CxPts (mpStr ℤ m n) σ₀) :
    y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U (pick M.isLB y) ⊓ mchart (ptC y)) :=
  mem_ptsIn_inf.2 ⟨mem_pick M.isLB y, mem_ptC y⟩


open Classical in
def hOf (z : (Σ k, Bk n k) → ℂ) : ℝ :=
  if hz : ∃ y, IsUnder y z then hval M a u hz.choose z (pick M.isLB hz.choose) (ptC hz.choose) else 0

theorem hOf_eq (h1 : (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ mchart c') (u i c'))) (h2 : (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ a k))
    (uniq : ∀ (z : (Σ k, Bk n k) → ℂ) (y y' : CxPts (mpStr ℤ m n) σ₀), IsUnder y z → IsUnder y' z → y = y')
    {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hy : IsUnder y z) (i : M.B.ι) (c : ∀ k, Bk n k)
    (hi : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c)) : hOf M a u z = hval M a u y z i c := by
  have hz : ∃ y, IsUnder y z := ⟨y, hy⟩
  rw [hOf, dite_eq_left hz, uniq z _ _ hz.choose_spec hy]
  have h0 := mem_pick_ptC M y
  rw [mem_ptsIn_inf] at h0 hi
  rw [hval_chart M a u h1 z (pick M.isLB y) i (ptC y) (mem_ptsIn_inf.2 h0) (mem_ptsIn_inf.2 ⟨hi.1, h0.2⟩),
    hval_multi M a u h2 hy i (ptC y) c (mem_ptsIn_inf.2 ⟨hi.1, h0.2⟩) (mem_ptsIn_inf.2 hi)]

theorem hval_pos {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hy : IsUnder y z) (i : M.B.ι)
    (c : ∀ k, Bk n k) (hi : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c)) : 0 < hval M a u y z i c := by
  have hz : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k =>
    ((hy k (c k)).1).1 (ptsIn_mono (mchart_le c k) (mem_ptsIn_inf.1 hi).2)
  refine mul_pos (mul_pos (Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hz k)) _)
    (norm_pos_iff.2 (ev_ne_zero hi (u i c).isUnit))) (Real.exp_pos _)

theorem hval_smul {y : CxPts (mpStr ℤ m n) σ₀} (z : (Σ k, Bk n k) → ℂ) (l : Fin (m + 1) → ℂ) (i : M.B.ι)
    (c : ∀ k, Bk n k) : hval M a u y (fun p => l p.1 * z p) i c = (∏ k, ‖l k‖ ^ a k) * hval M a u y z i c := by
  unfold hval
  simp only [norm_mul, mul_zpow, Finset.prod_mul_distrib]
  ring

def lineOf (h1 : (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ mchart c') (u i c'))) (h2 : (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ a k))
    (ex : ∀ (z : (Σ k, Bk n k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ y : CxPts (mpStr ℤ m n) σ₀, IsUnder y z)
    (uniq : ∀ (z : (Σ k, Bk n k) → ℂ) (y y' : CxPts (mpStr ℤ m n) σ₀), IsUnder y z → IsUnder y' z → y = y') :
    Geo.HermLine (Bk n) where
  a := a
  h := hOf M a u
  pos z hz := by
    obtain ⟨y, hy⟩ := ex z hz
    rw [hOf_eq M a u h1 h2 uniq hy _ _ (mem_pick_ptC M y)]
    exact hval_pos M a u hy _ _ (mem_pick_ptC M y)
  smul l z hl := by
    by_cases hz : ∃ y, IsUnder y z
    · obtain ⟨y, hy⟩ := hz
      rw [hOf_eq M a u h1 h2 uniq (isUnder_smul hy l hl) _ _ (mem_pick_ptC M y),
        hOf_eq M a u h1 h2 uniq hy _ _ (mem_pick_ptC M y), hval_smul]
    · have hz' : ¬ ∃ y, IsUnder y (fun p => l p.1 * z p) := fun ⟨y, hy⟩ => hz ⟨y, isUnder_of_smul l hl hy⟩
      rw [hOf, dite_eq_right hz', hOf, dite_eq_right hz, mul_zero]

theorem isHermRep_lineOf (h1 : (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ mchart c') (u i c'))) (h2 : (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ a k))
    (ex : ∀ (z : (Σ k, Bk n k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ y : CxPts (mpStr ℤ m n) σ₀, IsUnder y z)
    (uniq : ∀ (z : (Σ k, Bk n k) → ℂ) (y y' : CxPts (mpStr ℤ m n) σ₀), IsUnder y z → IsUnder y' z → y = y') :
    IsHermRep M (lineOf M a u h1 h2 ex uniq) :=
  ⟨u, h1, h2, fun i c _ _ hy hi => hOf_eq M a u h1 h2 uniq hy i c hi⟩

end Metric

theorem exists_isHermRep : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)), IsTwB M →
    ∃ A : Geo.HermLine (Bk n), IsHermRep M A := by
  intro m n M hM
  obtain ⟨c, t, ⟨hw⟩⟩ := hM
  obtain ⟨u, h1, h2⟩ := GlobalTheory.CompanionTheory.MPDict.TwUnits.exists_units m n M.B c t M.isLB hw
  exact ⟨_, isHermRep_lineOf M _ u h1 h2 (GlobalTheory.CompanionTheory.MPDict.UnderExists.exists_isUnder m n) (GlobalTheory.CompanionTheory.MPDict.isUnder_unique m n)⟩

end GlobalTheory.CompanionTheory.MPDict.HermRep
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvProdBlockUnit =====
