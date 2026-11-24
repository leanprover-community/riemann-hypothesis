module

public import Formalism.SharpRestriction.LevelLetterCocycles.CocyclesToWachVectorsBoundOfExtTool
public import Formalism.SharpRestriction.LevelLetterCocycles.IsTruncIff
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusDifferenceIdentity
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondLiftAtSituation
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

theorem second_lift_of_hypotheses [NeZero n] (W : LocWach PD LL O v n) (hZ : TTool2Z W)
    (hF : Formalism.MainNotions.CrystallineLiftingInputs.FTool W) (hB : Sh.BasTool W) (hK : Sh.LemK W) (hD : Sh.FilDim W)
    (hR : Sh.ExpRing W) (hE : Sh.ExpRules W)
    (h2a : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p2aK W T)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hEx : DcrisExactStrict PD LL)
    (hCs : CrysSubQuot PD LL) (hDq : DdREqDcris PD LL) : Step2 W := by
  intro d T₁ T₂ F b S η m hS
  obtain ⟨hDom, hDVR, hFr⟩ := hS.2.2.2.1
  refine ⟨2 * sigC PD.p (hpar n b S) η, Step2A.sigma_bound_le _ _ _ hS.2.1, ?_⟩
  intro s₁ FF _ _ _ _ g N y z μ ν hX F₁ ms hO
  exact second_lift_at_situation W hZ hF hB hK hD hR hE h2a h5 h9 hEx hCs hDq hS s₁ g N y z μ ν hX F₁ ms hO

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
