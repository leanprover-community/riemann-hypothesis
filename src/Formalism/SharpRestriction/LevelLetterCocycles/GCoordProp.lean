module

public import Formalism.SharpRestriction.LevelLetterCocycles.UniformizerUnitAndQFactor
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

def GCoordProp (W : LocWach PD LL O v n) : Prop :=
  ∀ (T : LocLat G Qp LL O) (i : ZMod n) (h c : ℕ) {r : ℕ} (e e' : Fin r → W.DD T)
    (_ : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T i e) (P Z : Matrix (Fin r) (Fin r) (PowerSeries O)),
    (∀ k, Formalism.MainNotions.LiftingTheory.qp W ^ h • W.φD T (e' k) = ∑ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (P m k) • e m) →
    PowerSeries.constantCoeff W.π₀₁ = 0 →
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) →
    ∀ (k : Fin r), Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE W T h c e' Z k ∈ W.N T →
      Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE W T h c e' Z k) →
      ∀ (a : Fin r → PowerSeries O),
        Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE W T h c e' Z k = ∑ l, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a l) • e l →
        ∀ l, (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ c * a l = (P * Z) l k

end Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord
