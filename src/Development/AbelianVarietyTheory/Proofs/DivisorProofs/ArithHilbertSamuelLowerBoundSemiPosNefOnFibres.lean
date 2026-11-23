module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSmallSectionsLeOfHermLBLeBySmallSectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermPairAdaptedTwistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSmallSecHermitianLineBundleArithVarietyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionTensorIsometricTransShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundleDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsLowerBoundAmpleMinusTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBall
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.LowerNef

theorem main : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L N : HermLB p) (a : ℝ), NefFib L → L.SemiPos D → L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (a / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) := by
  intro hAr hHS k _ X _ p D hX L N a hNef hSP hSI ε hε
  obtain ⟨P, b, s, t, c, hPL, hG, hGen, hReg, hLe⟩ := GlobalTheory.T.exists_goodHermPair_adapted_twist hAr hHS k X p D hX L N
  subst hPL
  have hlow := GlobalTheory.T.smallSections_lowerBound_ample_minus_twist hAr hHS k X p D hX P b s t hG c hGen hReg hNef hSP a hSI ε hε
  filter_upwards [hlow] with m hm
  obtain ⟨h1, h2, -⟩ := Pair.rep_base k X p P
  have hRep : P.Rep (m : ℤ) (-(c : ℤ)) ((P.L.pow m).tens ((P.A.pow c).dual)) := by
    have := Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_pow k X p P _ _ _ m h1)
      (Pair.rep_dual k X p P _ _ _ (Pair.rep_pow k X p P _ _ _ c h2))
    simpa using this
  have hE := SmallBall.encard_eq_Bl P hRep ((P.L.pow m).tens ((P.A.pow c).dual)).smallSec 1 zero_le_one fun u => by
    simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  have hle := GlobalTheory.T.encard_smallSections_le_of_hermLBLeBySmallSection k X p _ _ ((GlobalTheory.T.hermLBLeBySmallSection_tensor_isometric_trans_shift k X p _ _ (P.L.pow m)).1 hLe)
  have hfin := GlobalTheory.T.finite_smallSec_hermitian_line_bundle_arith_variety k X p D hX ((P.L.pow m).tens N)
  have hBle : (P.Bl m (-c) 1).encard ≤ ((P.L.pow m).tens N).smallSec.encard := hE ▸ hle
  have hBfin : (P.Bl m (-c) 1).Finite :=
    Set.finite_of_encard_le_coe (hBle.trans_eq hfin.cast_ncard_eq.symm)
  have hone : (1 : ℕ∞) ≤ (P.Bl m (-c) 1).encard :=
    hE ▸ Set.one_le_encard_iff_nonempty.2 ⟨_, ((P.L.pow m).tens ((P.A.pow c).dual)).zero_mem_smallSec⟩
  have hc1 : 1 ≤ (P.Bl m (-c) 1).ncard := by
    have := hBfin.cast_ncard_eq ▸ hone
    exact_mod_cast this
  have hc2 : (P.Bl m (-c) 1).ncard ≤ ((P.L.pow m).tens N).smallSec.ncard := by
    have := hBfin.cast_ncard_eq ▸ hfin.cast_ncard_eq ▸ hBle
    exact_mod_cast this
  refine hm.trans ?_
  unfold Pair.lc
  exact Real.log_le_log (by exact_mod_cast hc1) (by exact_mod_cast hc2)

end GlobalTheory.HSNef.LowerNef
