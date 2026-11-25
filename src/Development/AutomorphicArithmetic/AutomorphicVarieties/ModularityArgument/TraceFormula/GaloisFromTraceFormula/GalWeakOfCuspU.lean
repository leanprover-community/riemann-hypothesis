module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PInfAsc
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.PadicSubsetSums.StableGradedCounts.DegreeOneSplit
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
public import Mathlib.Topology.Algebra.MvPolynomial
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.FullThetaHolds
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FinIdx
public import Formalism.SharpRestriction.LevelLetterCocycles.LinearIndependentSmulOfNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LStrSat
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.TwistAbsPowAbsPow, Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.TameCongruences.LocallyConstantOneCochain, Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.GalWeakOfCuspU

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.TwistAbsPowAbsPow =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.TwistAbsPowAbsPow", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow\npublic import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PInfAsc\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.F.Rig

namespace GalX

open GlobalTheory.HeckeGal.Model (absPow absPow_isAbsPow)

theorem twist_absPow_absPow {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (P : CuspSub E a)
    (x y : ℝ) : (CG.mk (P.twist (absPow E x))).twist (absPow E y) = CG.mk (P.twist (absPow E (x + y))) := by
  rw [← absPow_mul_absPow]
  exact (CG.twist_mul (CG.mk P) _ _).symm

theorem infOfWeight_nodup {n : ℕ} (lam : DomWeight n) : (infOfWeight lam).Nodup := by
  unfold infOfWeight
  refine Multiset.Nodup.map (fun j k h => ?_) Finset.univ.nodup
  have h1 : (((lam.w j - (j : ℕ) : ℤ)) : ℂ) = ((lam.w k - (k : ℕ) : ℤ) : ℂ) := by
    push_cast
    linear_combination h
  have h2 : lam.w j - (j : ℕ) = lam.w k - (k : ℕ) := Int.cast_injective h1
  rcases lt_trichotomy j k with hjk | rfl | hjk
  · have := lam.anti hjk.le
    have : (j : ℕ) < k := hjk
    omega
  · rfl
  · have := lam.anti hjk.le
    have : (k : ℕ) < j := hjk
    omega

theorem mem_infOfWeight {n : ℕ} {lam : DomWeight n} {z : ℂ} (hz : z ∈ infOfWeight lam) :
    ∃ k : ℤ, z = k + ((n : ℂ) - 1) / 2 := by
  unfold infOfWeight at hz
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
  exact ⟨lam.w j - (j : ℕ), by push_cast; ring⟩

theorem regTw {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (D : Pre E n) (hr : D.Reg)
    (i : Fin D.c) {a d : ℕ} (P : CuspSub E a) (he : AscEmb (D.V i) P d) (k : Fin d) :
    (CG.mk (P.twist (absPow E (spehExp d k + ((a : ℝ) - n) / 2)))).IsRegAlg := by
  refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_
  obtain ⟨lam, hlam⟩ := hr τ
  obtain ⟨m0, hm0, hsum⟩ := infAsc_holds E (D.N i) a d (D.V i) P (D.discrete i) he τ _ (D.inf i τ)
  set s : ℝ := spehExp d k + ((a : ℝ) - n) / 2 with hs
  have hexpo : ∀ τ, expo (absPow E s) τ = s :=
    (GlobalTheory.CuspRep.InfType.expo_of_infType E _).2.1 s (absPow_isAbsPow E s)
  have hm' : (P.twist (absPow E s)).HasInfChar τ (m0.map (· + (s : ℂ))) := by
    have := hm0.twist (absPow E s)
    rwa [hexpo] at this
  rw [CG.HasInfChar.infChar_eq (π := CG.mk _) hm']
  have hle : D.m i τ ≤ infOfWeight lam := by
    rw [← hlam]
    exact Finset.single_le_sum (f := fun j => D.m j τ) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)
  have hk : m0.map (· + (spehExp d k : ℂ)) ≤ D.m i τ := by
    rw [hsum]
    exact Finset.single_le_sum (f := fun j : Fin d => m0.map (· + (spehExp d j : ℂ))) (fun _ _ => Multiset.zero_le _)
      (Finset.mem_univ k)
  have hnd : (m0.map (· + (spehExp d k : ℂ))).Nodup := Multiset.nodup_of_le (hk.trans hle) (infOfWeight_nodup lam)
  refine ⟨(Multiset.Nodup.of_map _ hnd).map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨j, hj⟩ := mem_infOfWeight (Multiset.mem_of_le (hk.trans hle) (Multiset.mem_map_of_mem _ hy))
  refine ⟨j, ?_⟩
  rw [hs]
  push_cast
  linear_combination hj

end GalX

end PositivityTheory.Rg.BcB.F.Rig

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.TwistAbsPowAbsPow =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.TameCongruences.LocallyConstantOneCochain =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.TameCongruences.LocallyConstantOneCochain", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary\npublic import Formalism.PadicSubsetSums.StableGradedCounts.DegreeOneSplit\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\npublic import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Mathlib.Topology.Algebra.MvPolynomial\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.DzCong

end PositivityTheory.Rg.DzCong

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.TameCongruences.LocallyConstantOneCochain =====

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.GalWeakOfCuspU =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.GalWeakOfCuspU", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.GalStepOfHyp\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModel\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc\npublic import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.FullThetaHolds\nimport Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LStrSat\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.TwistAbsPowAbsPow\npublic import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.TameCongruences.LocallyConstantOneCochain\npublic import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FinIdx\npublic import Formalism.SharpRestriction.LevelLetterCocycles.LinearIndependentSmulOfNeZero\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Connected.Separation\nimport Mathlib.Topology.MetricSpace.Ultra.TotallySeparated\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rig PositivityTheory.Rg.BcB.F.Rig.GalX
open GlobalTheory.HeckeGal.Model (absPow absPow_isAbsPow)

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

def GalAt (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (N : ℕ) : Prop :=
  ∀ a : ℕ, 1 ≤ a → a ≤ N → ∀ P : CuspSub E a, P.IsCsd → ∀ s : ℝ, (CG.mk (P.twist (absPow E s))).IsRegAlg →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧
      ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
        ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), (P.twist (absPow E s)).IsLocComp w σ →
        ∀ S : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w σ.ρ S → ∀ (B : ValuationSubring Ω) (g : G E Ω),
          IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g →
          (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
            X - C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((-((1 - (a : ℝ)) / 2) : ℝ) : ℂ)))).prod

def GalWeak (N : ℕ) : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∃ (l : ℕ) (_ : Fact l.Prime) (ι : Qbar l ≃+* ℂ), GalAt E (AlgebraicClosure E) ι N

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.GalWeakOfCuspU =====
