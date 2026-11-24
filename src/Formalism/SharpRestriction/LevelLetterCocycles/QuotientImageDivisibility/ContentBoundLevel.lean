module

public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSAddLeft
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

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def ContentBoundLevel [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m → ∀ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d,
    ∃ κ : ℤ, (κ : ℝ) ≤ (((b c + S : ℕ) : ℝ) + 1) / ((PD.p : ℝ) - 1) + 2 +
        Formalism.MainNotions.RamifiedCoefficientChains.S9.EG PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S) η S +
        Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig₂ PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) +
        ((b (c - 1 - 1) + S : ℕ) : ℝ) - (b (c - 1) : ℝ) + 1 ∧
    ∀ ell ∈ (fun z => φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) z)) ''
        Formalism.MainNotions.CrystallineLiftingInputs.Dlat W T₂ (c - 1 - 1 - 1),
      ell ∈ FilCris PD T₂.ρ (b (c - 1) : ℤ) →
      ∃ y : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c y ∧
        ∃ hB : W.Q ^ (b c + S) • W.map F y ∈ W.N T₂,
        ∀ (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ (u : PowerSeries LL),
          W.lev c ζ W.q = X * u → constantCoeff u ≠ 0 →
        ∀ (dd : ℤ → T₂.V ⊗[Qp] BdR), (∃ m₀, LB m₀ dd) →
          W.levN T₂ c ζ ⟨W.Q ^ (b c + S) • W.map F y, hB⟩ = smulS ((X * u) ^ (b c + S)) dd →
          (∀ i : ℤ, i < ((b c + S : ℕ) : ℤ) → i ≠ 0 → dd i = 0) ∧
          dd 0 = ((PD.p : LL) ^ κ) • ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) ell) ∧
          ∀ i : ℤ, dd i ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ c

end Formalism.MainNotions.N.Pv.LocalLengthBound
