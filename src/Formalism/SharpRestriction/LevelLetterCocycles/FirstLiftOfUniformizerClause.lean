module

public import Formalism.SharpRestriction.LevelLetterCocycles.CocyclesToWachVectorsBoundOfExtTool
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool
public import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.FirstLiftOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.RToolModDStab
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem first_lift_of_uniformizer_clause [NeZero n] (W : LocWach PD LL O v n) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing O v)
    (h9 : Formalism.MainNotions.LiftingTheory.P9π₀ W) (hRN : Formalism.MainNotions.LiftingTheory.CaseA W → Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DssLet W) (hEx : Sh.ExpRules W) (hER : Sh.ExpRing W)
    (hK : Sh.LemK W) (hFD : Sh.FilDim W) (hB : Sh.BasTool W) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : Step1 W :=
  first_lift_of_hypotheses W hV h9 hRN (rToolMod_dStab W hP9) hD hEx hER hK hFD hB hE hC hQ

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
