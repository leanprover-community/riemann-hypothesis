module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitTripleEquations.SplitTriOf
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.SecondConstantHolds
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdealAlt
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Reduction
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.GaussDegenerate
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.MulIntegerMemBaseLattice
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopIso
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.TripleSumIndep
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSmulMemLattice
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.HomLMulPres
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.GMConjTranspose
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SplitPair
public import Formalism.LocalToGlobal.GlobalTheory.GL3.LinkThetaStatementFamily
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen
public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitPairGen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Mathlib.Tactic.Linter.HaveILetI

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitTripleEquations.EqPOfSplit, Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.RightMoveTrianglesOfUnit, Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.RowSwApply, Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.RightMoveTrianglesHold, Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.PolFamInhabited, Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.ExistsNOne, Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SumThreeComm, Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SqSplitOf, Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.EqPOfPair, Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairOfGen, Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.EqPAll, Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Outright

-- ===== clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitTripleEquations.EqPOfSplit =====
-- clump-header: {"m": "Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitTripleEquations.EqPOfSplit", "h": "module\n\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitTripleEquations.SplitTriOf\npublic import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.SecondConstantHolds\nimport Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdealAlt\nimport Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.Sq

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem sqP_of {B : Ker.Base D cc δ} (hL : B.LatAll) (hS : SqSplit B) : SqP D B.tor := by
  intro N N' L L₁ L' L'' hN hN' h1 h2 h3 h4 G hG
  obtain ⟨A, A', hP⟩ := hS N N' L L₁ L' L'' hN hN' h1 h2 h3 h4
  by_cases hG0 : G = 0
  · subst hG0
    funext v
    simp [TaylorLogMetric.Iop, TaylorLogMetric.U]
  have hF : ∃ F ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L L'), F ≠ 0 := ⟨G, fun x hx z => hG.2 x hx z, hG0⟩
  have tripleData_of {N N' : ℕ}
      {L₁ L₂ L₃ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
      {L₁' L₂' L₃' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
      (a1 : TaylorLogMetric.admitted D N N' L₁ L₁')
      (a2 : TaylorLogMetric.admitted D N N' L₂ L₂')
      (a3 : TaylorLogMetric.admitted D N N' L₃ L₃') :
      TripleData (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N')
        (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L₁ L₁')
        (TaylorLogMetric.La D B.tor L₂ L₂') (TaylorLogMetric.La D B.tor L₃ L₃') := by
    exact {
      herm := formV_herm' _ _ _ _
      sd₁ := (hL.1 N N' _ _ a1).1
      sd₂ := (hL.1 N N' _ _ a2).1
      sd₃ := (hL.1 N N' _ _ a3).1
      sc₁ := (hL.1 N N' _ _ a1).2
      sc₂ := (hL.1 N N' _ _ a2).2
      sc₃ := (hL.1 N N' _ _ a3).2
      i₁₂ := (hL.2 N N' _ _ _ _ a1 a2).1
      i₂₁ := (hL.2 N N' _ _ _ _ a1 a2).2
      i₁₃ := (hL.2 N N' _ _ _ _ a1 a3).1
      i₃₁ := (hL.2 N N' _ _ _ _ a1 a3).2
      i₂₃ := (hL.2 N N' _ _ _ _ a2 a3).1
      i₃₂ := (hL.2 N N' _ _ _ _ a2 a3).2 }
  have hT1 := tripleData_of (admissible_of_integral_conj_le hN hN' h1 h3) (admissible_of_integral_conj_le hN hN' h2 h3) (admissible_of_integral_conj_le hN hN' h2 h4)
  have hT2 := tripleData_of (admissible_of_integral_conj_le hN hN' h1 h3) (admissible_of_integral_conj_le hN hN' h1 h4) (admissible_of_integral_conj_le hN hN' h2 h4)
  obtain ⟨S₂, S₃, hS₂, hS₃, hμ⟩ :=
    mu_one_of_split hT1 (splitTri_of hP (false, false) (true, false) (true, true) hT1) hF
  obtain ⟨T₂, T₃, hT₂, hT₃, hν⟩ :=
    mu_one_of_split hT2 (splitTri_of hP (false, false) (false, true) (true, true) hT2) hF
  funext v
  have e1 := tripleFormula _ _ _ _ _ _ hT1 S₂ S₃ hS₂ hS₃ G (fun x hx z => hG.2 x hx z) v
  have e2 := tripleFormula _ _ _ _ _ _ hT2 T₂ T₃ hT₂ hT₃ G (fun x hx z => hG.2 x hx z) v
  rw [hμ, one_mul] at e1
  rw [hν, one_mul] at e2
  exact e1.trans e2.symm

theorem eqP_of_split (B : Ker.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ)
    (hSp : SqSplit B) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) : B.EqP χ :=
  J.eqP_of_paths B hcc hδ hδ0 hS χ hχ (sqP_of (B.latAll hcc hδ hδ0) hSp) hTL hTR

end Formalism.L2.PairingIndexBounds.Eq.Sq
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitTripleEquations.EqPOfSplit =====

-- ===== clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.RightMoveTrianglesOfUnit =====
-- clump-header: {"m": "Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.RightMoveTrianglesOfUnit", "h": "module\n\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Reduction\npublic import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.GaussDegenerate\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdealAlt\npublic import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions Formalism.L2.Th1.H

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def MuOneL (B : Ker.Base D cc δ) : Prop :=
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → Even N' → SD D L → SD D L₁ →
    ∃ S₂ S₃ : Finset (TaylorLogMetric.VC D N N'),
      IsReps (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) S₂ ∧
      IsReps (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) S₃ ∧
      tripleMu (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N'))
        (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) S₂ S₃ = 1

def MuOneR (B : Ker.Base D cc δ) : Prop :=
  ∀ N N' (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Even N → Even N' → SD D L' → SD D L'' →
    ∃ S₂ S₃ : Finset (TaylorLogMetric.VC D N N'),
      IsReps (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') S₂ ∧
      IsReps (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L'') S₃ ∧
      tripleMu (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L')
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L'') S₂ S₃ = 1

theorem tripleData_of {B : Ker.Base D cc δ} (hL : B.LatAll) {N N' : ℕ}
    {L₁ L₂ L₃ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L₁' L₂' L₃' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (a1 : TaylorLogMetric.admitted D N N' L₁ L₁') (a2 : TaylorLogMetric.admitted D N N' L₂ L₂') (a3 : TaylorLogMetric.admitted D N N' L₃ L₃') :
    TripleData (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L₁ L₁') (TaylorLogMetric.La D B.tor L₂ L₂') (TaylorLogMetric.La D B.tor L₃ L₃') :=
  { herm := formV_herm' _ _ _ _
    sd₁ := (hL.1 N N' _ _ a1).1
    sd₂ := (hL.1 N N' _ _ a2).1
    sd₃ := (hL.1 N N' _ _ a3).1
    sc₁ := (hL.1 N N' _ _ a1).2
    sc₂ := (hL.1 N N' _ _ a2).2
    sc₃ := (hL.1 N N' _ _ a3).2
    i₁₂ := (hL.2 N N' _ _ _ _ a1 a2).1
    i₂₁ := (hL.2 N N' _ _ _ _ a1 a2).2
    i₁₃ := (hL.2 N N' _ _ _ _ a1 a3).1
    i₃₁ := (hL.2 N N' _ _ _ _ a1 a3).2
    i₂₃ := (hL.2 N N' _ _ _ _ a2 a3).1
    i₃₂ := (hL.2 N N' _ _ _ _ a2 a3).2 }

theorem left_move_triangles_of_unit {B : Ker.Base D cc δ} (hL : B.LatAll) (hM : MuOneL B) : Tr0L D B.tor := by
  intro N N' L L₁ hN hN' h1 h2 G hG
  obtain ⟨S₂, S₃, hS₂, hS₃, hμ⟩ := hM N N' L L₁ hN hN' h1 h2
  have hT := tripleData_of hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' h1 (sd0 N')) (admissible_of_integral_conj_le hN hN' h2 (sd0 N'))
  funext v
  have := tripleFormula _ _ _ _ _ _ hT S₂ S₃ hS₂ hS₃ G (fun x hx z => hG.2 x hx z) v
  rw [hμ, one_mul] at this
  exact this

theorem right_move_triangles_of_unit {B : Ker.Base D cc δ} (hL : B.LatAll) (hM : MuOneR B) : Tr0R D B.tor := by
  intro N N' L' L'' hN hN' h1 h2 G hG
  obtain ⟨S₂, S₃, hS₂, hS₃, hμ⟩ := hM N N' L' L'' hN hN' h1 h2
  have hT := tripleData_of hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' (sd0 N) h1) (admissible_of_integral_conj_le hN hN' (sd0 N) h2)
  funext v
  have := tripleFormula _ _ _ _ _ _ hT S₂ S₃ hS₂ hS₃ G (fun x hx z => hG.2 x hx z) v
  rw [hμ, one_mul] at this
  exact this

end Formalism.L2.PairingIndexBounds.Eq
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.RightMoveTrianglesOfUnit =====

-- ===== clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.RowSwApply =====
-- clump-header: {"m": "Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.RowSwApply", "h": "module\n\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.MulIntegerMemBaseLattice\npublic import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopIso\nimport Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.Mu

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem yy_stab {N N' : ℕ} {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (f : Matrix (Fin N') (Fin N) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin N') (Fin N) D.host.E)
    (hfE : ∀ (a : D.host.E) A, f (a • A) = a • f A)
    (hgen : ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ x ∈ M, A *ᵥ x ∈ M') → ∀ x ∈ M, f A *ᵥ x ∈ M')
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ TaylorLogMetric.YYl D M M') : f A ∈ TaylorLogMetric.YYl D M M' := by
  have hH : TaylorLogMetric.homL D M M' ≤ (TaylorLogMetric.homL D M M').comap f :=
    Submodule.span_le.2 fun B hB => Submodule.subset_span (hgen B hB)
  have hY : TaylorLogMetric.YYl D M M' ≤ (TaylorLogMetric.YYl D M M').comap f := by
    refine Submodule.span_le.2 fun B hB => ?_
    obtain ⟨a, ha, A', hA', rfl⟩ := hB
    show f (a • A') ∈ TaylorLogMetric.YYl D M M'
    rw [hfE]
    exact Submodule.subset_span ⟨a, ha, f A', hH hA', rfl⟩
  exact hY hA

theorem la_stab {N N' : ℕ} (T : TaylorLogMetric.Tor D) {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (Φ : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N')
    (f : Matrix (Fin N') (Fin N) D.host.E → Matrix (Fin N') (Fin N) D.host.E)
    (hΦ : ∀ (w : ℂ) A, Φ (w • TaylorLogMetric.embV D T A) = w • TaylorLogMetric.embV D T (f A))
    (hf : ∀ A ∈ TaylorLogMetric.YYl D M M', f A ∈ TaylorLogMetric.YYl D M M') {z : TaylorLogMetric.VC D N N'} (hz : z ∈ TaylorLogMetric.La D T M M') :
    Φ z ∈ TaylorLogMetric.La D T M M' := by
  unfold TaylorLogMetric.La at hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hv
    rw [hΦ]
    exact AddSubgroup.subset_closure ⟨w, hw, f A, hf A hA, rfl⟩
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact AddSubgroup.neg_mem _ hx

theorem mulO_apply {N N' : ℕ} (r : D.host.E) (x : TaylorLogMetric.VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    J.mulO N N' r x τ i j = TaylorLogMetric.embT D τ r * x τ i j := rfl

theorem mulO_la {N N' : ℕ} (T : TaylorLogMetric.Tor D) (hT : ∀ τ x, T.emb τ x = TaylorLogMetric.embT D τ x)
    {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (r : 𝓞 D.host.E) {z : TaylorLogMetric.VC D N N'} (hz : z ∈ TaylorLogMetric.La D T M M') :
    J.mulO N N' (r : D.host.E) z ∈ TaylorLogMetric.La D T M M' := by
  refine la_stab T (J.mulO N N' (r : D.host.E)).toAddMonoidHom (fun A => (r : D.host.E) • A) ?_ ?_ hz
  · intro w A
    funext τ i j
    simp only [LinearMap.toAddMonoidHom_coe, mulO_apply, TaylorLogMetric.embV, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, hT]
    rw [map_mul]; ring
  · intro A hA
    rw [show (r : D.host.E) • A = r • A from algebraMap_smul D.host.E r A]
    exact Submodule.smul_mem _ r hA

theorem mem_stdL {n : ℕ} {v : Fin n → D.host.E} :
    v ∈ StandardLatticesGL3.stdL D n ↔ ∀ i, v i ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp [StandardLatticesGL3.stdL, Submodule.mem_pi]

def swp (n : ℕ) (i : Fin n) : Fin n :=
  ⟨if i.val < n / 2 then i.val + n / 2 else i.val - n / 2, by have := i.isLt; split_ifs <;> omega⟩

theorem swp_val (n : ℕ) (i : Fin n) :
    (swp n i).val = if i.val < n / 2 then i.val + n / 2 else i.val - n / 2 := rfl

theorem swp_swp {n : ℕ} (h : Even n) (i : Fin n) : swp n (swp n i) = i := by
  obtain ⟨k, hk⟩ := h
  apply Fin.ext
  rw [swp_val, swp_val]
  have := i.isLt
  split_ifs <;> omega

theorem swp_lt {n : ℕ} (h : Even n) (i : Fin n) : (swp n i).val < n / 2 ↔ ¬ i.val < n / 2 := by
  obtain ⟨k, hk⟩ := h
  rw [swp_val]; have := i.isLt
  split_ifs <;> omega

def swpE {n : ℕ} (h : Even n) : Equiv.Perm (Fin n) := Function.Involutive.toPerm (swp n) (swp_swp h)

def rowP (N N' : ℕ) : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => if i.val < N' / 2 then z τ i j else 0
  map_zero' := by funext τ i j; simp
  map_add' x y := by funext τ i j; simp only [Pi.add_apply]; split_ifs <;> simp

def rowSw (N N' : ℕ) : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => z τ (swp N' i) j
  map_zero' := rfl
  map_add' _ _ := rfl

def colP (N N' : ℕ) : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => if j.val < N / 2 then z τ i j else 0
  map_zero' := by funext τ i j; simp
  map_add' x y := by funext τ i j; simp only [Pi.add_apply]; split_ifs <;> simp

def colSw (N N' : ℕ) : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => z τ i (swp N j)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem rowP_apply {N N' : ℕ} (z : TaylorLogMetric.VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    rowP N N' z τ i j = if i.val < N' / 2 then z τ i j else 0 := rfl
theorem rowSw_apply {N N' : ℕ} (z : TaylorLogMetric.VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    rowSw N N' z τ i j = z τ (swp N' i) j := rfl
theorem colP_apply {N N' : ℕ} (z : TaylorLogMetric.VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    colP N N' z τ i j = if j.val < N / 2 then z τ i j else 0 := rfl
theorem colSw_apply {N N' : ℕ} (z : TaylorLogMetric.VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    colSw N N' z τ i j = z τ i (swp N j) := rfl

section Facts

variable {N N' : ℕ}

theorem rowProjection_rowProjection (x : TaylorLogMetric.VC D N N') : rowP N N' (rowP N N' x) = rowP N N' x := by
  funext τ i j; simp only [rowP_apply]; split_ifs <;> rfl
theorem colP_colP (x : TaylorLogMetric.VC D N N') : colP N N' (colP N N' x) = colP N N' x := by
  funext τ i j; simp only [colP_apply]; split_ifs <;> rfl

theorem rowProjection_orthogonal (A : ℝ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (rowP N N' x) (y - rowP N N' y) = 0 := by
  rw [Ker.formV_apply, Finset.sum_eq_zero, zero_div]
  intro τ _; refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  simp only [rowP_apply, Pi.sub_apply]; split_ifs <;> simp
theorem colP_orth (A : ℝ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (colP N N' x) (y - colP N N' y) = 0 := by
  rw [Ker.formV_apply, Finset.sum_eq_zero, zero_div]
  intro τ _; refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  simp only [colP_apply, Pi.sub_apply]; split_ifs <;> simp

theorem rowSw_sw (h : Even N') (x : TaylorLogMetric.VC D N N') : rowSw N N' (rowSw N N' x) = x := by
  funext τ i j; simp only [rowSw_apply, swp_swp h]
theorem colSw_sw (h : Even N) (x : TaylorLogMetric.VC D N N') : colSw N N' (colSw N N' x) = x := by
  funext τ i j; simp only [colSw_apply, swp_swp h]

theorem rowSw_p (h : Even N') (x : TaylorLogMetric.VC D N N') :
    rowP N N' (rowSw N N' x) = rowSw N N' x - rowSw N N' (rowP N N' x) := by
  funext τ i j
  simp only [rowP_apply, rowSw_apply, Pi.sub_apply]
  have := swp_lt h i
  split_ifs <;> simp_all
theorem colSw_p (h : Even N) (x : TaylorLogMetric.VC D N N') :
    colP N N' (colSw N N' x) = colSw N N' x - colSw N N' (colP N N' x) := by
  funext τ i j
  simp only [colP_apply, colSw_apply, Pi.sub_apply]
  have := swp_lt h j
  split_ifs <;> simp_all

theorem rowSw_form (h : Even N') (A : ℝ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (rowSw N N' x) (rowSw N N' y) = Ker.formV A D.what₂.Tau N N' x y := by
  rw [Ker.formV_apply, Ker.formV_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  exact Equiv.sum_comp (swpE h) (fun i => ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j))
theorem colSw_form (h : Even N) (A : ℝ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (colSw N N' x) (colSw N N' y) = Ker.formV A D.what₂.Tau N N' x y := by
  rw [Ker.formV_apply, Ker.formV_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp (swpE h) (fun j => x τ i j * (starRingEnd ℂ) (y τ i j))

theorem al_form (T : TaylorLogMetric.Tor D) (f : TaylorLogMetric.VC D N N' → TaylorLogMetric.VC D N N')
    (hf : ∀ x y, Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (f x) (f y) = Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' x y)
    (x : TaylorLogMetric.VC D N N') : TaylorLogMetric.al D T (f x) = TaylorLogMetric.al D T x := by
  unfold TaylorLogMetric.al
  rw [Ker.Hf_eq, Ker.Hf_eq, hf]

theorem mulO_rowP (r : D.host.E) (x : TaylorLogMetric.VC D N N') :
    J.mulO N N' r (rowP N N' x) = rowP N N' (J.mulO N N' r x) := by
  funext τ i j; simp only [mulO_apply, rowP_apply]; split_ifs <;> simp
theorem mulO_colP (r : D.host.E) (x : TaylorLogMetric.VC D N N') :
    J.mulO N N' r (colP N N' x) = colP N N' (J.mulO N N' r x) := by
  funext τ i j; simp only [mulO_apply, colP_apply]; split_ifs <;> simp

end Facts

section Lat

variable {N N' : ℕ}

def rowPM (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun A := Matrix.of fun i j => if i.val < N' / 2 then A i j else 0
  map_add' A B := by refine Matrix.ext fun i j => ?_; simp only [of_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c A := by refine Matrix.ext fun i j => ?_; simp only [of_apply, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp

def rowSwM (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun A := Matrix.of fun i j => A (swp N' i) j
  map_add' A B := by ext i j; simp
  map_smul' c A := by ext i j; simp

def colPM (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun A := Matrix.of fun i j => if j.val < N / 2 then A i j else 0
  map_add' A B := by refine Matrix.ext fun i j => ?_; simp only [of_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c A := by refine Matrix.ext fun i j => ?_; simp only [of_apply, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp

def colSwM (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun A := Matrix.of fun i j => A i (swp N j)
  map_add' A B := by ext i j; simp
  map_smul' c A := by ext i j; simp

variable (T : TaylorLogMetric.Tor D) (hT : ∀ τ x, T.emb τ x = TaylorLogMetric.embT D τ x)
include hT

theorem rowProjection_mem_lattice {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {z : TaylorLogMetric.VC D N N'}
    (hz : z ∈ TaylorLogMetric.La D T M (StandardLatticesGL3.stdL D N')) : rowP N N' z ∈ TaylorLogMetric.La D T M (StandardLatticesGL3.stdL D N') := by
  refine la_stab T (rowP N N') (rowPM N N') ?_ (fun A hA => yy_stab (rowPM N N') ?_ ?_ hA) hz
  · intro w A; funext τ i j
    simp only [rowP_apply, rowPM, LinearMap.coe_mk, AddHom.coe_mk, TaylorLogMetric.embV, Pi.smul_apply, smul_eq_mul, of_apply, hT]
    split_ifs <;> simp
  · intro a A; refine Matrix.ext fun i j => ?_
    simp only [rowPM, LinearMap.coe_mk, AddHom.coe_mk, of_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp
  · intro A hA x hx
    have h := mem_stdL.1 (hA x hx)
    refine mem_stdL.2 fun i => ?_
    by_cases hi : i.val < N' / 2
    · have e : (rowPM N N' A *ᵥ x) i = (A *ᵥ x) i := by
        simp only [rowPM, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, of_apply, if_pos hi]
      rw [e]; exact h i
    · have e : (rowPM N N' A *ᵥ x) i = 0 := by
        simp only [rowPM, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, of_apply, if_neg hi, zero_mul,
          Finset.sum_const_zero]
      rw [e]; exact Submodule.zero_mem _

theorem rowSw_la {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {z : TaylorLogMetric.VC D N N'}
    (hz : z ∈ TaylorLogMetric.La D T M (StandardLatticesGL3.stdL D N')) : rowSw N N' z ∈ TaylorLogMetric.La D T M (StandardLatticesGL3.stdL D N') := by
  refine la_stab T (rowSw N N') (rowSwM N N') ?_ (fun A hA => yy_stab (rowSwM N N') ?_ ?_ hA) hz
  · intro w A; funext τ i j; rfl
  · intro a A; ext i j; rfl
  · intro A hA x hx
    have h := mem_stdL.1 (hA x hx)
    exact mem_stdL.2 fun i => h (swp N' i)

theorem colP_mem_la {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {z : TaylorLogMetric.VC D N N'}
    (hz : z ∈ TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) M') : colP N N' z ∈ TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) M' := by
  refine la_stab T (colP N N') (colPM N N') ?_ (fun A hA => yy_stab (colPM N N') ?_ ?_ hA) hz
  · intro w A; funext τ i j
    simp only [colP_apply, colPM, LinearMap.coe_mk, AddHom.coe_mk, TaylorLogMetric.embV, Pi.smul_apply, smul_eq_mul, of_apply, hT]
    split_ifs <;> simp
  · intro a A; refine Matrix.ext fun i j => ?_
    simp only [colPM, LinearMap.coe_mk, AddHom.coe_mk, of_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp
  · intro A hA x hx
    have hx' : (fun j : Fin N => if j.val < N / 2 then x j else 0) ∈ StandardLatticesGL3.stdL D N := by
      refine mem_stdL.2 fun j => ?_
      split_ifs
      · exact mem_stdL.1 hx j
      · exact Submodule.zero_mem _
    have e : colPM N N' A *ᵥ x = A *ᵥ (fun j : Fin N => if j.val < N / 2 then x j else 0) := by
      funext i
      simp only [colPM, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, of_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    rw [e]; exact hA _ hx'

theorem colSw_la (hN : Even N) {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {z : TaylorLogMetric.VC D N N'}
    (hz : z ∈ TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) M') : colSw N N' z ∈ TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) M' := by
  refine la_stab T (colSw N N') (colSwM N N') ?_ (fun A hA => yy_stab (colSwM N N') ?_ ?_ hA) hz
  · intro w A; funext τ i j; rfl
  · intro a A; ext i j; rfl
  · intro A hA x hx
    have hx' : (fun j : Fin N => x (swp N j)) ∈ StandardLatticesGL3.stdL D N := mem_stdL.2 fun j => mem_stdL.1 hx (swp N j)
    have e : colSwM N N' A *ᵥ x = A *ᵥ (fun j : Fin N => x (swp N j)) := by
      funext i
      simp only [colSwM, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, of_apply]
      have := Equiv.sum_comp (swpE hN) (fun j => A i j * x (swp N j))
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      show A i (swp N j) * x j = A i (swp N j) * x (swp N (swp N j))
      rw [swp_swp hN]
    rw [e]; exact hA _ hx'

end Lat

section Mult

variable {N N' : ℕ}

theorem mulO_mul (r r' : D.host.E) (x : TaylorLogMetric.VC D N N') :
    J.mulO N N' r (J.mulO N N' r' x) = J.mulO N N' (r * r') x := by
  funext τ i j; simp only [mulO_apply, map_mul]; ring

theorem form_mul (A : ℝ) (l s : D.host.E) (n : ℕ) (hl : star l * l = -1 + (n : D.host.E) * s)
    (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (J.mulO N N' l x) (J.mulO N N' l y)
      = -Ker.formV A D.what₂.Tau N N' x y + (n : ℂ) * Ker.formV A D.what₂.Tau N N' x (J.mulO N N' s y) := by
  rw [J.mulO_adj, mulO_mul, hl]
  have : J.mulO N N' (-1 + (n : D.host.E) * s) y = -y + n • J.mulO N N' s y := by
    funext τ i j
    simp only [mulO_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, map_add (f := _), map_neg, map_one, map_mul, map_natCast]
    simp only [nsmul_eq_mul]
    ring
  rw [this, map_add (f := _), map_neg, map_nsmul, nsmul_eq_mul]

theorem al_mul (T : TaylorLogMetric.Tor D) {La' : AddSubgroup (TaylorLogMetric.VC D N N')} (hI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt T La')
    (l s : D.host.E) (e : ℕ) (hl : star l * l = -1 + ((4 * e : ℕ) : D.host.E) * s) {x : TaylorLogMetric.VC D N N'}
    (hx : x ∈ La') (hmx : J.mulO N N' l x ∈ La') (hsx : J.mulO N N' s x ∈ La') :
    TaylorLogMetric.al D T (J.mulO N N' l x) = TaylorLogMetric.al D T x := by
  obtain ⟨m0, h0re, h0r⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.self_int T hI hx
  obtain ⟨m1, h1re, h1r⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.self_int T hI hmx
  obtain ⟨a, b, -, hab⟩ := hI x hx _ hsx
  have hf : TaylorLogMetric.Hf D T (J.mulO N N' l x) (J.mulO N N' l x)
      = -TaylorLogMetric.Hf D T x x + ((4 * e : ℕ) : ℂ) * TaylorLogMetric.Hf D T x (J.mulO N N' s x) :=
    form_mul (TaylorLogMetric.area T.abelian₂) l s (4 * e) hl x x
  rw [hab] at hf
  have hre : (TaylorLogMetric.Hf D T (J.mulO N N' l x) (J.mulO N N' l x)).re
      = -(TaylorLogMetric.Hf D T x x).re + ((4 * e : ℕ) : ℝ) * (a / Real.sqrt D.host.d) := by
    rw [hf, Complex.add_re, Complex.neg_re,
      show ((4 * e : ℕ) : ℂ) = (((4 * e : ℕ) : ℝ) : ℂ) by norm_cast, Complex.re_ofReal_mul]
    simp
  have key : (m1 : ℝ) = -m0 + 2 * e * a := by
    rw [h1re, h0re] at hre
    have hs := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D
    field_simp at hre
    push_cast at hre
    linarith
  have key' : m1 = -m0 + 2 * e * a := by exact_mod_cast key
  unfold TaylorLogMetric.al
  rw [h1r, h0r]
  apply Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.neg_one_zpow_congr
  rw [key']
  exact ⟨-m0 + e * a, by ring⟩

theorem altE_mul (T : TaylorLogMetric.Tor D) {La' : AddSubgroup (TaylorLogMetric.VC D N N')} (hI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt T La')
    (l s : D.host.E) (e : ℕ) (hl : star l * l = -1 + ((4 * e : ℕ) : D.host.E) * s) {z y : TaylorLogMetric.VC D N N'}
    (hez : e • z ∈ La') (hsy : J.mulO N N' s y ∈ La') :
    ∃ k : ℤ, altE (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (J.mulO N N' l z) (J.mulO N N' l y)
      = -altE (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') z y + 2 * k := by
  obtain ⟨a, b, -, hab⟩ := hI _ hez _ hsy
  have hb : (e : ℝ) * (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' z (J.mulO N N' s y)).im = b := by
    have h1 : Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (e • z) (J.mulO N N' s y)
        = ((e : ℝ) : ℂ) * Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' z (J.mulO N N' s y) := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, map_smul, LinearMap.smul_apply, smul_eq_mul]; push_cast; ring
    have h2 := congrArg Complex.im hab
    rw [show TaylorLogMetric.Hf D T (e • z) (J.mulO N N' s y)
        = Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (e • z) (J.mulO N N' s y) from rfl, h1,
      Complex.im_ofReal_mul] at h2
    rw [h2]; simp
  have hf := form_mul (TaylorLogMetric.area T.abelian₂) l s (4 * e) hl z y
  refine ⟨2 * b, ?_⟩
  unfold altE
  rw [hf, Complex.add_im, Complex.neg_im,
    show ((4 * e : ℕ) : ℂ) = (((4 * e : ℕ) : ℝ) : ℂ) by norm_cast, Complex.im_ofReal_mul]
  push_cast
  linarith [hb]

theorem mulO_inv (l s l' : D.host.E) (e : ℕ) (hl : star l * l = -1 + ((4 * e : ℕ) : D.host.E) * s)
    (hl' : l' = star l) (x : TaylorLogMetric.VC D N N') :
    J.mulO N N' (-l') (J.mulO N N' l x) = x + e • J.mulO N N' (-4 * s) x ∧
    J.mulO N N' l (J.mulO N N' (-l') x) = x + e • J.mulO N N' (-4 * s) x := by
  have hE : -l' * l = 1 + (e : D.host.E) * (-4 * s) := by
    rw [hl', neg_mul, hl]; push_cast; ring
  constructor
  · funext τ i j
    have := congrArg (TaylorLogMetric.embT D τ) hE
    simp only [map_mul, map_add (f := _), map_one, map_natCast, map_neg, map_ofNat] at this
    simp only [mulO_apply, Pi.add_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul, map_mul, map_neg, map_ofNat]
    linear_combination x τ i j * this
  · funext τ i j
    have := congrArg (TaylorLogMetric.embT D τ) hE
    simp only [map_mul, map_add (f := _), map_one, map_natCast, map_neg, map_ofNat] at this
    simp only [mulO_apply, Pi.add_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul, map_mul, map_neg, map_ofNat]
    linear_combination x τ i j * this

end Mult

end Formalism.L2.PairingIndexBounds.Eq.Mu
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.RowSwApply =====

-- ===== clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.RightMoveTrianglesHold =====
-- clump-header: {"m": "Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.RightMoveTrianglesHold", "h": "module\n\npublic import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopIso\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.MulIntegerMemBaseLattice\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.RightMoveTrianglesOfUnit\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.TripleSumIndep\nimport Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep\nimport Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.SecondConstantHolds\nimport Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdealAlt\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.RowSwApply\nimport Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.Mu

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem signData_of (T : TaylorLogMetric.Tor D) {N N' : ℕ} {Λ₁ Λ₂ Λ₃ : AddSubgroup (TaylorLogMetric.VC D N N')}
    (p σ : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N') (pp : ∀ x, p (p x) = p x)
    (porth : ∀ x y, Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (p x) (y - p y) = 0)
    (σσ : ∀ x, σ (σ x) = x) (σp : ∀ x, p (σ x) = σ x - σ (p x))
    (σH : ∀ x y, Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (σ x) (σ y) = Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' x y)
    (hmp : ∀ (r : D.host.E) x, J.mulO N N' r (p x) = p (J.mulO N N' r x))
    (hΛ : ∀ Λ, Λ = Λ₁ ∨ Λ = Λ₂ ∨ Λ = Λ₃ → (∀ x ∈ Λ, p x ∈ Λ) ∧ (∀ x ∈ Λ, σ x ∈ Λ) ∧
      (∀ (r : 𝓞 D.host.E), ∀ x ∈ Λ, J.mulO N N' (r : D.host.E) x ∈ Λ) ∧ Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt T Λ)
    (e : ℕ) (e21 : ∀ x ∈ Λ₂, e • x ∈ Λ₁) (e31 : ∀ x ∈ Λ₃, e • x ∈ Λ₁) (e32 : ∀ x ∈ Λ₃, e • x ∈ Λ₂)
    (l s l' : 𝓞 D.host.E) (hl : star (l : D.host.E) * l = -1 + ((4 * e : ℕ) : D.host.E) * s)
    (hl' : (l' : D.host.E) = star (l : D.host.E)) :
    SignData (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D T) Λ₁ Λ₂ Λ₃ p σ
      (J.mulO N N' (l : D.host.E)).toAddMonoidHom (J.mulO N N' (-(l' : D.host.E))).toAddMonoidHom
      (J.mulO N N' (-4 * (s : D.host.E))).toAddMonoidHom e := by
  obtain ⟨p1, σ1, m1, I1⟩ := hΛ Λ₁ (Or.inl rfl)
  obtain ⟨p2, σ2, m2, I2⟩ := hΛ Λ₂ (Or.inr (Or.inl rfl))
  obtain ⟨p3, σ3, m3, I3⟩ := hΛ Λ₃ (Or.inr (Or.inr rfl))
  have mn : ∀ {Λ : AddSubgroup (TaylorLogMetric.VC D N N')}, (∀ (r : 𝓞 D.host.E), ∀ x ∈ Λ, J.mulO N N' (r : D.host.E) x ∈ Λ) →
      ∀ x ∈ Λ, J.mulO N N' (-(l' : D.host.E)) x ∈ Λ := fun h x hx => by
    have := h (-l') x hx; simpa using this
  have mr : ∀ {Λ : AddSubgroup (TaylorLogMetric.VC D N N')}, (∀ (r : 𝓞 D.host.E), ∀ x ∈ Λ, J.mulO N N' (r : D.host.E) x ∈ Λ) →
      ∀ x ∈ Λ, J.mulO N N' (-4 * (s : D.host.E)) x ∈ Λ := fun h x hx => by
    have := h (-(s + s + s + s)) x hx
    rwa [show ((-(s + s + s + s) : 𝓞 D.host.E) : D.host.E) = -4 * (s : D.host.E) by push_cast; ring] at this
  exact
  { pp := pp, porth := porth, p1 := p1, p2 := p2, p3 := p3
    σσ := σσ, σp := σp, σH := σH, σα := fun x => al_form T σ σH x
    σ1 := σ1, σ2 := σ2, σ3 := σ3
    mp := fun x => hmp _ x, m'p := fun x => hmp _ x
    m1 := m1 l, m2 := m2 l, m3 := m3 l
    m'1 := mn m1, m'2 := mn m2, m'3 := mn m3
    r2 := mr m2, r3 := mr m3
    inv := fun x => (mulO_inv (l : D.host.E) (s : D.host.E) (l' : D.host.E) e hl hl' x).1
    inv' := fun x => (mulO_inv (l : D.host.E) (s : D.host.E) (l' : D.host.E) e hl hl' x).2
    e21 := e21, e31 := e31, e32 := e32
    mα1 := fun x hx => al_mul T I1 (l : D.host.E) (s : D.host.E) e hl hx (m1 l x hx) (m1 s x hx)
    mα2 := fun x hx => al_mul T I2 (l : D.host.E) (s : D.host.E) e hl hx (m2 l x hx) (m2 s x hx)
    mα3 := fun x hx => al_mul T I3 (l : D.host.E) (s : D.host.E) e hl hx (m3 l x hx) (m3 s x hx)
    mH := fun z hz y hy => altE_mul T I2 (l : D.host.E) (s : D.host.E) e hl (e32 z hz) (m2 s y hy) }

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem muOneL_of (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (B : Ker.Base D cc δ)
    (hS : B.StdOK) : MuOneL B := by
  intro N N' L L₁ hN hN' hL hL₁
  have hLat := B.latAll hcc hδ h0
  have a1 := admissible_of_integral_conj_le (D := D) hN hN' (sd0 N) (sd0 N')
  have a2 := admissible_of_integral_conj_le (D := D) hN hN' hL (sd0 N')
  have a3 := admissible_of_integral_conj_le (D := D) hN hN' hL₁ (sd0 N')
  have hT : TripleData (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) := by
    exact ⟨formV_herm' _ _ _ _, (hLat.1 N N' _ _ a1).1, (hLat.1 N N' _ _ a2).1,
      (hLat.1 N N' _ _ a3).1, (hLat.1 N N' _ _ a1).2, (hLat.1 N N' _ _ a2).2,
      (hLat.1 N N' _ _ a3).2, (hLat.2 N N' _ _ _ _ a1 a2).1,
      (hLat.2 N N' _ _ _ _ a1 a2).2, (hLat.2 N N' _ _ _ _ a1 a3).1,
      (hLat.2 N N' _ _ _ _ a1 a3).2, (hLat.2 N N' _ _ _ _ a2 a3).1,
      (hLat.2 N N' _ _ _ _ a2 a3).2⟩
  obtain ⟨S₂, hS₂⟩ := (repsExist _ _ _ hT.i₁₂).1
  obtain ⟨S₃, hS₃⟩ := (repsExist _ _ _ hT.i₂₃).1
  refine ⟨S₂, S₃, hS₂, hS₃, ?_⟩
  obtain ⟨e, he, e21, e31, e32⟩ := exists_e hT
  obtain ⟨l, s, -, hl⟩ := J.negOneNorm D (4 * e) (by omega)
  obtain ⟨l', hl'⟩ := J.star_int l
  have hF : ∃ F ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')), F ≠ 0 :=
    ⟨B.thZero N N', (B.thZeroMem hS N N').2, B.thZero_ne_zero hS N N'⟩
  have hemb : ∀ τ x, (B.tor).emb τ x = TaylorLogMetric.embT D τ x := fun _ _ => rfl
  refine tripleMu_eq_one hT hF (signData_of B.tor (rowP N N') (rowSw N N') rowProjection_rowProjection (rowProjection_orthogonal _) (rowSw_sw hN')
    (rowSw_p hN') (rowSw_form hN' _) mulO_rowP ?_ e e21 e31 e32 l s l' hl hl') hS₂ hS₃
  intro Λ hΛ
  rcases hΛ with rfl | rfl | rfl
  · exact ⟨fun x hx => rowProjection_mem_lattice B.tor hemb hx, fun x hx => rowSw_la B.tor hemb hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N'))⟩
  · exact ⟨fun x hx => rowProjection_mem_lattice B.tor hemb hx, fun x hx => rowSw_la B.tor hemb hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' hL (sd0 N'))⟩
  · exact ⟨fun x hx => rowProjection_mem_lattice B.tor hemb hx, fun x hx => rowSw_la B.tor hemb hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' hL₁ (sd0 N'))⟩

theorem muOneR_of (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (B : Ker.Base D cc δ)
    (hS : B.StdOK) : MuOneR B := by
  intro N N' L' L'' hN hN' hL' hL''
  have hLat := B.latAll hcc hδ h0
  have a1 := admissible_of_integral_conj_le (D := D) hN hN' (sd0 N) (sd0 N')
  have a2 := admissible_of_integral_conj_le (D := D) hN hN' (sd0 N) hL'
  have a3 := admissible_of_integral_conj_le (D := D) hN hN' (sd0 N) hL''
  have hT : TripleData (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L'') := by
    exact ⟨formV_herm' _ _ _ _, (hLat.1 N N' _ _ a1).1, (hLat.1 N N' _ _ a2).1,
      (hLat.1 N N' _ _ a3).1, (hLat.1 N N' _ _ a1).2, (hLat.1 N N' _ _ a2).2,
      (hLat.1 N N' _ _ a3).2, (hLat.2 N N' _ _ _ _ a1 a2).1,
      (hLat.2 N N' _ _ _ _ a1 a2).2, (hLat.2 N N' _ _ _ _ a1 a3).1,
      (hLat.2 N N' _ _ _ _ a1 a3).2, (hLat.2 N N' _ _ _ _ a2 a3).1,
      (hLat.2 N N' _ _ _ _ a2 a3).2⟩
  obtain ⟨S₂, hS₂⟩ := (repsExist _ _ _ hT.i₁₂).1
  obtain ⟨S₃, hS₃⟩ := (repsExist _ _ _ hT.i₂₃).1
  refine ⟨S₂, S₃, hS₂, hS₃, ?_⟩
  obtain ⟨e, he, e21, e31, e32⟩ := exists_e hT
  obtain ⟨l, s, -, hl⟩ := J.negOneNorm D (4 * e) (by omega)
  obtain ⟨l', hl'⟩ := J.star_int l
  have hF : ∃ F ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')), F ≠ 0 :=
    ⟨B.thZero N N', (B.thZeroMem hS N N').2, B.thZero_ne_zero hS N N'⟩
  have hemb : ∀ τ x, (B.tor).emb τ x = TaylorLogMetric.embT D τ x := fun _ _ => rfl
  refine tripleMu_eq_one hT hF (signData_of B.tor (colP N N') (colSw N N') colP_colP (colP_orth _) (colSw_sw hN)
    (colSw_p hN) (colSw_form hN _) mulO_colP ?_ e e21 e31 e32 l s l' hl hl') hS₂ hS₃
  intro Λ hΛ
  rcases hΛ with rfl | rfl | rfl
  · exact ⟨fun x hx => colP_mem_la B.tor hemb hx, fun x hx => colSw_la B.tor hemb hN hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N'))⟩
  · exact ⟨fun x hx => colP_mem_la B.tor hemb hx, fun x hx => colSw_la B.tor hemb hN hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' (sd0 N) hL')⟩
  · exact ⟨fun x hx => colP_mem_la B.tor hemb hx, fun x hx => colSw_la B.tor hemb hN hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' (sd0 N) hL'')⟩

theorem left_move_triangles_hold (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (B : Ker.Base D cc δ)
    (hS : B.StdOK) : Tr0L D B.tor :=
  left_move_triangles_of_unit (B.latAll hcc hδ h0) (muOneL_of hcc hδ h0 B hS)

theorem right_move_triangles_hold (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (B : Ker.Base D cc δ)
    (hS : B.StdOK) : Tr0R D B.tor :=
  right_move_triangles_of_unit (B.latAll hcc hδ h0) (muOneR_of hcc hδ h0 B hS)

end Formalism.L2.PairingIndexBounds.Eq.Mu
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.RightMoveTrianglesHold =====

-- ===== clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.PolFamInhabited =====
-- clump-header: {"m": "Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.PolFamInhabited", "h": "module\n\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitTripleEquations.SplitTriOf\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitTripleEquations.EqPOfSplit\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.RightMoveTrianglesHold\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem eqP_top (B : Ker.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hSp : Sq.SqSplit B) : B.EqP χ :=
  Sq.eqP_of_split B hcc hδ hδ0 hS χ hχ hSp (Mu.left_move_triangles_hold hcc hδ hδ0 B hS) (Mu.right_move_triangles_hold hcc hδ hδ0 B hS)

end Formalism.L2.PairingIndexBounds.Eq
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.PolFamInhabited =====

-- ===== clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.ExistsNOne =====
-- clump-header: {"m": "Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.ExistsNOne", "h": "module\n\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Reduction\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSmulMemLattice\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.HomLMulPres\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.MainNotions Formalism.L2.PairingIndexBounds.Eq

variable {D : D7}

theorem mul_smul_mem {N : ℕ} {L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {m k : 𝓞 D.host.E}
    {v : Fin N → D.host.E} (h : (k : D.host.E) • v ∈ L₁) : ((m * k : 𝓞 D.host.E) : D.host.E) • v ∈ L₁ := by
  have e : ((m * k : 𝓞 D.host.E) : D.host.E) • v = m • ((k : D.host.E) • v) := by
    rw [osmul, smul_smul]
    norm_cast
  rw [e]
  exact L₁.smul_mem m h

theorem exists_n_one {N : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : L.FG)
    (hsp : Submodule.span D.host.E (L₁ : Set (Fin N → D.host.E)) = ⊤) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ ∀ u ∈ L, (n : D.host.E) • u ∈ L₁ := by
  obtain ⟨s, hs⟩ := hL
  choose f hf0 hf using _root_.UpperTheory.Reformulated.B.ExistsIntegerSmulMemOfSpanEqTop.exists_smul_mem hsp
  refine ⟨∏ g ∈ s, f g, Finset.prod_ne_zero_iff.2 fun g _ => hf0 g, ?_⟩
  intro u hu
  rw [← hs] at hu
  induction hu using Submodule.span_induction with
  | mem g hg =>
    rw [← Finset.prod_erase_mul s f hg]
    exact mul_smul_mem (hf g)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact L₁.add_mem hx hy
  | smul c x _ hx =>
    rw [osmul c x, smul_comm, ← osmul]
    exact L₁.smul_mem c hx

theorem exists_n {N : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L) (hL1 : SD D L₁) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ (∀ u ∈ L, (n : D.host.E) • u ∈ L₁) ∧ ∀ u ∈ L₁, (n : D.host.E) • u ∈ L := by
  obtain ⟨hfg, hsp, -⟩ := hL
  obtain ⟨hfg1, hsp1, -⟩ := hL1
  obtain ⟨a, ha, h1⟩ := exists_n_one hfg hsp1
  obtain ⟨b, hb, h2⟩ := exists_n_one hfg1 hsp
  refine ⟨b * a, mul_ne_zero hb ha, fun u hu => mul_smul_mem (h1 u hu), fun u hu => ?_⟩
  rw [mul_comm]
  exact mul_smul_mem (h2 u hu)

end Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.ExistsNOne =====

-- ===== clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SumThreeComm =====
-- clump-header: {"m": "Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SumThreeComm", "h": "module\n\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.HomLMulPres\npublic import Formalism.LocalToGlobal.KernelLattices.LateralTheory\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.GMConjTranspose\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.MainNotions Formalism.L2.PairingIndexBounds.Eq Formalism.L2.Th1.H

variable {D : D7}

theorem sum_three_comm {a b c : ℕ} (F : Fin a → Fin b → Fin c → ℂ) :
    ∑ i, ∑ j, ∑ k, F i j k = ∑ k, ∑ j, ∑ i, F i j k := by
  calc ∑ i, ∑ j, ∑ k, F i j k = ∑ i, ∑ k, ∑ j, F i j k := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, F i j k := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, F i j k := Finset.sum_congr rfl fun k _ => Finset.sum_comm

theorem formV_phi {N N' : ℕ} (A : ℝ) (M : Matrix (Fin N') (Fin N') D.host.E) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (phi M x) y =
      Ker.formV A D.what₂.Tau N N' x (phi (letI := D.host.cmStar; Mᴴ) y) := by
  let _ := D.host.cmStar
  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, phi_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_

  simp only [Finset.sum_mul, map_sum, map_mul, Finset.mul_sum, conjTranspose_apply, embT_star']
  rw [sum_three_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [starRingEnd_apply, star_star]
  ring

variable (D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ)

def HH : Sesq (TaylorLogMetric.VC D N N') := Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N'

def qq (x : TaylorLogMetric.VC D N N') : ℝ := Real.sqrt D.host.d / 2 * (HH D cc δ N N' x x).re

def cp (x y : TaylorLogMetric.VC D N N') : ℝ :=
  Real.sqrt D.host.d / 2 * ((HH D cc δ N N' x y).re + (HH D cc δ N N' y x).re)

def bet (x y : TaylorLogMetric.VC D N N') : ℝ := cp D cc δ N N' x y - (HH D cc δ N N' x y).im

def Good (x y : TaylorLogMetric.VC D N N') : Prop := ∃ k : ℤ, bet D cc δ N N' x y = 2 * k

variable {D cc δ N N'}

theorem qq_add (x y : TaylorLogMetric.VC D N N') :
    qq D cc δ N N' (x + y) = qq D cc δ N N' x + qq D cc δ N N' y + cp D cc δ N N' x y := by
  simp only [qq, cp, map_add (f := _), LinearMap.add_apply, Complex.add_re]
  ring

theorem bet_add_left (x x' y : TaylorLogMetric.VC D N N') :
    bet D cc δ N N' (x + x') y = bet D cc δ N N' x y + bet D cc δ N N' x' y := by
  simp only [bet, cp, map_add (f := _), LinearMap.add_apply, Complex.add_re, Complex.add_im]
  ring

theorem bet_add_right (x y y' : TaylorLogMetric.VC D N N') :
    bet D cc δ N N' x (y + y') = bet D cc δ N N' x y + bet D cc δ N N' x y' := by
  simp only [bet, cp, map_add (f := _), LinearMap.add_apply, Complex.add_re, Complex.add_im]
  ring

theorem bet_phi (e : Matrix (Fin N') (Fin N') D.host.E) (x y : TaylorLogMetric.VC D N N') :
    bet D cc δ N N' (phi e x) (phi e y) = bet D cc δ N N' x (phi (letI := D.host.cmStar; eᴴ * e) y) := by
  letI := D.host.cmStar
  have h1 : HH D cc δ N N' (phi e x) (phi e y) = HH D cc δ N N' x (phi (eᴴ * e) y) := by
    unfold HH
    rw [formV_phi, phi_mul]
  have h2 : HH D cc δ N N' (phi e y) (phi e x) = HH D cc δ N N' (phi (eᴴ * e) y) x := by
    unfold HH
    rw [formV_phi, formV_phi, ← phi_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  unfold bet cp
  rw [h1, h2]

theorem negpow (b : ℤ) : ((-1 : ℂ) ^ b) = Complex.exp ((Real.pi : ℂ) * Complex.I * (b : ℂ)) := by
  rw [show (Real.pi : ℂ) * Complex.I * (b : ℂ) = (b : ℂ) * ((Real.pi : ℂ) * Complex.I) by ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem al_of_q {z : TaylorLogMetric.VC D N N'} {m : ℤ} (h : qq D cc δ N N' z = m) : TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) z = (-1 : ℂ) ^ m := by
  show (-1 : ℂ) ^ (round (qq D cc δ N N' z)) = _
  rw [h, round_intCast]

theorem good_of_law {x y : TaylorLogMetric.VC D N N'} {mx my mxy : ℤ} (hx : qq D cc δ N N' x = mx) (hy : qq D cc δ N N' y = my)
    (hxy : qq D cc δ N N' (x + y) = mxy)
    (hlaw : TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (x + y) = TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x * TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) y *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE (HH D cc δ N N') x y : ℂ))) :
    Good D cc δ N N' x y := by
  rw [al_of_q hxy, al_of_q hx, al_of_q hy, negpow, negpow, negpow, ← Complex.exp_add,
    ← Complex.exp_add] at hlaw
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hlaw
  have hq := qq_add (D := D) (cc := cc) (δ := δ) x y
  rw [hx, hy, hxy] at hq
  refine ⟨n, ?_⟩
  have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have h2 : (mxy : ℂ) = mx + my + (altE (HH D cc δ N N') x y : ℂ) + 2 * n := by
    apply mul_left_cancel₀ hpi
    linear_combination hn
  have h3 : (mxy : ℝ) = mx + my + altE (HH D cc δ N N') x y + 2 * n := by
    exact_mod_cast h2
  simp only [bet, altE] at h3 ⊢
  linarith

theorem law_of_good {x y : TaylorLogMetric.VC D N N'} {mx my mxy : ℤ} (hx : qq D cc δ N N' x = mx) (hy : qq D cc δ N N' y = my)
    (hxy : qq D cc δ N N' (x + y) = mxy) (hg : Good D cc δ N N' x y) :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (x + y) = TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x * TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) y *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE (HH D cc δ N N') x y : ℂ)) := by
  obtain ⟨k, hk⟩ := hg
  rw [al_of_q hxy, al_of_q hx, al_of_q hy, negpow, negpow, negpow, ← Complex.exp_add,
    ← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨k, ?_⟩
  have hq := qq_add (D := D) (cc := cc) (δ := δ) x y
  rw [hx, hy, hxy] at hq
  simp only [bet] at hk
  have h4 : (mxy : ℝ) = mx + my + altE (HH D cc δ N N') x y + 2 * k := by
    simp only [altE]
    linarith
  have h5 : (mxy : ℂ) = mx + my + (altE (HH D cc δ N N') x y : ℂ) + 2 * k := by
    exact_mod_cast h4
  rw [h5]
  ring

theorem good_of_lat {Y : AddSubgroup (TaylorLogMetric.VC D N N')} (hsc : IsSemiChar (HH D cc δ N N') Y (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)))
    (hq : ∀ z ∈ Y, ∃ m : ℤ, qq D cc δ N N' z = m) {x y : TaylorLogMetric.VC D N N'} (hx : x ∈ Y) (hy : y ∈ Y) :
    Good D cc δ N N' x y := by
  obtain ⟨mx, hmx⟩ := hq x hx
  obtain ⟨my, hmy⟩ := hq y hy
  obtain ⟨mxy, hmxy⟩ := hq (x + y) (Y.add_mem hx hy)
  exact good_of_law hmx hmy hmxy (hsc.2 x hx y hy)

end Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SumThreeComm =====

-- ===== clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SqSplitOf =====
-- clump-header: {"m": "Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SqSplitOf", "h": "module\n\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitTripleEquations.SplitTriOf\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SplitPair\npublic import Formalism.LocalToGlobal.GlobalTheory.GL3.LinkThetaStatementFamily\nimport Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdealAlt\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.ExistsNOne\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SumThreeComm\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.MainNotions Formalism.L2.PairingIndexBounds.Eq Formalism.L2.Th1.H

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem good3 {a b c t : ℝ} (h : t = a + b + c) (ha : ∃ k : ℤ, a = 2 * k) (hb : ∃ k : ℤ, b = 2 * k)
    (hc : ∃ k : ℤ, c = 2 * k) : ∃ k : ℤ, t = 2 * k := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  obtain ⟨z, rfl⟩ := hc
  exact ⟨x + y + z, by rw [h]; push_cast; ring⟩

theorem sqSplit_of (B : Ker.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hP : SplitPair D) : Sq.SqSplit B := by
  intro N N' L L₁ L' L'' hN hN' h1 h2 h3 h4
  obtain ⟨n, hn0, hnL, hnL1⟩ := exists_n h1 h2
  obtain ⟨e, heL', heL'', hM⟩ := hP N' L' L'' hN' h3 h4 n hn0
  have hAdm : ∀ i : Bool × Bool, TaylorLogMetric.admitted D N N' (if i.1 then L₁ else L) (if i.2 then L'' else L') := by
    rintro ⟨a, b⟩
    cases a <;> cases b
    · exact admissible_of_integral_conj_le hN hN' h1 h3
    · exact admissible_of_integral_conj_le hN hN' h1 h4
    · exact admissible_of_integral_conj_le hN hN' h2 h3
    · exact admissible_of_integral_conj_le hN hN' h2 h4
  have hq : ∀ i, ∀ z ∈ Sq.sqFam B.tor L L₁ L' L'' i, ∃ m : ℤ, qq D cc δ N N' z = m := fun i z hz =>
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B N N' _ _ (hAdm i) z hz
  have hsc : ∀ i, IsSemiChar (HH D cc δ N N') (Sq.sqFam B.tor L L₁ L' L'' i) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) :=
    fun i => ((B.latAll hcc hδ hδ0).1 N N' _ _ (hAdm i)).2
  have hn : ∀ a c : Bool, ∀ u ∈ (if c then L₁ else L), (n : D.host.E) • u ∈ (if a then L₁ else L) := by
    intro a c u hu
    cases a <;> cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at hu ⊢
    · rw [← osmul]; exact L.smul_mem n hu
    · exact hnL1 u hu
    · exact hnL u hu
    · rw [← osmul]; exact L₁.smul_mem n hu
  have hor : ∀ b : Bool, ∀ y ∈ (if b then L'' else L'), y ∈ L' ∨ y ∈ L'' := by
    intro b y hy
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hy
    · exact Or.inl hy
    · exact Or.inr hy
  have hin : ∀ d : Bool, ∀ m, m ∈ L' → m ∈ L'' → m ∈ (if d then L'' else L') := by
    intro d m hm1 hm2
    cases d <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact hm1
    · exact hm2
  have he : ∀ b : Bool, ∀ y ∈ (if b then L'' else L'), e *ᵥ y ∈ (if b then L'' else L') := by
    intro b y hy
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hy ⊢
    · exact heL' y hy
    · exact heL'' y hy
  have hpres : ∀ i, ∀ z ∈ Sq.sqFam B.tor L L₁ L' L'' i, phi e z ∈ Sq.sqFam B.tor L L₁ L' L'' i := by
    intro i z hz
    exact phi_La (yy_mul fun A hA => homL_mul_pres (he i.2) hA) z hz
  have hMin : ∀ M ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
      (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)),
      ∀ i j, ∀ z ∈ Sq.sqFam B.tor L L₁ L' L'' i, phi M z ∈ Sq.sqFam B.tor L L₁ L' L'' j := by
    intro M hMs i j z hz
    refine phi_La (yy_mul fun A hA => homL_mul_min hn0 (hn i.1 j.1) ?_ hA) z hz
    intro y hy
    obtain ⟨m, hm1, hm2, hm⟩ := hM M hMs y (hor i.2 y hy)
    exact ⟨m, hin j.2 m hm1 hm2, hm⟩
  have hM1 : e * e - e ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
      (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)) :=
    Set.mem_insert _ _
  have hM2 : (letI := D.host.cmStar; eᴴ) * e ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
      (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hM3 : (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e) ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
      (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

  have hidem : ∀ x : TaylorLogMetric.VC D N N', phi e x - phi e (phi e x) = -(phi (e * e - e) x) := by
    intro x
    rw [phi_sub, phi_mul]
    abel
  have hone : ∀ x : TaylorLogMetric.VC D N N', x - phi e x = phi (1 - e) x := by
    intro x
    rw [phi_sub, phi_one]
  refine ⟨AddSubgroup.comap (AddMonoidHom.id _ - phi e) (⨅ i, Sq.sqFam B.tor L L₁ L' L'' i),
    AddSubgroup.comap (phi e) (⨅ i, Sq.sqFam B.tor L L₁ L' L'' i), ?_⟩
  have hA : ∀ x, x ∈ AddSubgroup.comap (AddMonoidHom.id _ - phi e) (⨅ i, Sq.sqFam B.tor L L₁ L' L'' i) ↔
      ∀ i, x - phi e x ∈ Sq.sqFam B.tor L L₁ L' L'' i := by
    intro x
    simp [AddSubgroup.mem_iInf]
  have hA' : ∀ x, x ∈ AddSubgroup.comap (phi e) (⨅ i, Sq.sqFam B.tor L L₁ L' L'' i) ↔
      ∀ i, phi e x ∈ Sq.sqFam B.tor L L₁ L' L'' i := by
    intro x
    simp [AddSubgroup.mem_iInf]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hx' i
    have := (Sq.sqFam B.tor L L₁ L' L'' i).add_mem ((hA x).1 hx i) ((hA' x).1 hx' i)
    rwa [sub_add_cancel] at this
  · intro i x hx
    refine ⟨phi e x, (hA _).2 fun j => ?_, x - phi e x, (hA' _).2 fun j => ?_, hpres i x hx,
      (Sq.sqFam B.tor L L₁ L' L'' i).sub_mem hx (hpres i x hx), (add_sub_cancel _ _).symm⟩
    · rw [hidem]
      exact (Sq.sqFam B.tor L L₁ L' L'' j).neg_mem (hMin _ hM1 i j x hx)
    · rw [map_sub, hidem]
      exact (Sq.sqFam B.tor L L₁ L' L'' j).neg_mem (hMin _ hM1 i j x hx)
  · intro x y hx hy i j k hxi hyj hxy
    obtain ⟨mx, hmx⟩ := hq i x hxi
    obtain ⟨my, hmy⟩ := hq j y hyj
    obtain ⟨mxy, hmxy⟩ := hq k (x + y) hxy
    refine law_of_good hmx hmy hmxy ?_
    have key : bet D cc δ N N' x y = bet D cc δ N N' (phi e x) (phi e y) +
        bet D cc δ N N' (phi e x) (y - phi e y) + bet D cc δ N N' (x - phi e x) y := by
      have h := bet_add_left (cc := cc) (δ := δ) (phi e x) (x - phi e x) y
      have h' := bet_add_right (cc := cc) (δ := δ) (phi e x) (phi e y) (y - phi e y)
      rw [add_sub_cancel] at h h'
      rw [h, h']
    refine good3 key ?_ ?_ ?_
    · rw [bet_phi]
      exact good_of_lat (hsc i) (hq i) hxi (hMin _ hM2 j i y hyj)
    · exact good_of_lat (hsc i) (hq i) (hpres i x hxi) ((hA y).1 hy i)
    · exact good_of_lat (hsc j) (hq j) ((hA x).1 hx j) hyj
  · intro x y hx hy i j k hxi hyj hxy
    obtain ⟨mx, hmx⟩ := hq i x hxi
    obtain ⟨my, hmy⟩ := hq j y hyj
    obtain ⟨mxy, hmxy⟩ := hq k (x + y) hxy
    refine law_of_good hmx hmy hmxy ?_
    have key : bet D cc δ N N' x y = bet D cc δ N N' (x - phi e x) (y - phi e y) +
        bet D cc δ N N' (x - phi e x) (phi e y) + bet D cc δ N N' (phi e x) y := by
      have h := bet_add_left (cc := cc) (δ := δ) (x - phi e x) (phi e x) y
      have h' := bet_add_right (cc := cc) (δ := δ) (x - phi e x) (y - phi e y) (phi e y)
      rw [sub_add_cancel] at h h'
      rw [h, h']
    refine good3 key ?_ ?_ ?_
    · rw [hone x, hone y, bet_phi]
      exact good_of_lat (hsc i) (hq i) hxi (hMin _ hM3 j i y hyj)
    · exact good_of_lat (hsc i) (hq i) ((Sq.sqFam B.tor L L₁ L' L'' i).sub_mem hxi ((hA' x).1 hx i)) ((hA' y).1 hy i)
    · exact good_of_lat (hsc j) (hq j) ((hA' x).1 hx j) hyj

end Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SqSplitOf =====

-- ===== clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.EqPOfPair =====
-- clump-header: {"m": "Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.EqPOfPair", "h": "module\n\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SplitPair\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.PolFamInhabited\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SqSplitOf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.MainNotions

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem eqP_of_pair (B : Ker.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hP : SplitPair D) : B.EqP χ :=
  eqP_top B hcc hδ hδ0 hS χ hχ (sqSplit_of B hcc hδ hδ0 hP)

end Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.EqPOfPair =====

-- ===== clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairOfGen =====
-- clump-header: {"m": "Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairOfGen", "h": "module\n\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SplitPair\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.EqPOfPair\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open NumberField Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.SqG

theorem splitPair_of_gen (h : SplitPairGen) (D : Formalism.BasicNotions.D7) : SquareSplitPairs.SplitPair D := by
  letI := D.host.cmStar
  intro N' L' L'' hN h1 h2 n hn
  exact h D.host.E D.sp.cm.cmUnram N' L' L'' hN h1 h2 n hn

theorem eqP_gen {D : Formalism.BasicNotions.D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ)
    (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0) (hS : B.StdOK)
    (χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ) (hχ : Formalism.MainNotions.TaylorLogMetric.IsChi D χ) (hG : SplitPairGen) : B.EqP χ :=
  SquareSplitPairs.eqP_of_pair B hcc hδ hδ0 hS χ hχ (splitPair_of_gen hG D)

end Formalism.L2.PairingIndexBounds.Eq.SqG
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairOfGen =====

-- ===== clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.EqPAll =====
-- clump-header: {"m": "Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.EqPAll", "h": "module\n\npublic import Formalism.LocalToGlobal.KernelLattices.LateralTheory\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen\npublic import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairOfGen\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.L2.PairingIndexBounds.Eq.SqG

theorem eqP_all {D : Formalism.BasicNotions.D7} {cc : Ideal (NumberField.RingOfIntegers D.host.K)} {δ : ℂ}
    (B : Formalism.L2.Ker.Base D cc δ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (hS : B.StdOK) (χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ) (hχ : Formalism.MainNotions.TaylorLogMetric.IsChi D χ) (hP : SplitPairGen) : B.EqP χ := by
  have hδ0 : δ ≠ 0 := by
    intro h0
    apply Formalism.L2.PairingIndexBounds.Rec.discrNZ D cc hcc
    rw [← hδ, h0]
    norm_num
  exact eqP_gen B hcc hδ hδ0 hS χ hχ hP

end Formalism.L2.PairingIndexBounds.Eq.SqG
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.EqPAll =====

-- ===== clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Outright =====
-- clump-header: {"m": "Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Outright", "h": "module\n\npublic import Formalism.LocalToGlobal.KernelLattices.LateralTheory\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.EqPAll\npublic import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitPairGen\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.L2.PairingIndexBounds.Eq.SqG

theorem eqP_outright {D : Formalism.BasicNotions.D7} {cc : Ideal (NumberField.RingOfIntegers D.host.K)} {δ : ℂ}
    (B : Formalism.L2.Ker.Base D cc δ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (hS : B.StdOK) (χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ) (hχ : Formalism.MainNotions.TaylorLogMetric.IsChi D χ) : B.EqP χ :=
  eqP_all B hcc hδ hS χ hχ split_pair_generation

end Formalism.L2.PairingIndexBounds.Eq.SqG
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Outright =====
