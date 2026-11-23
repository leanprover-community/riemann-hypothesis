module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameSphericalDoubleCosetRepsLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.standardFrame_sphericalDoubleCoset_reps_local : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (Ψ : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ψ → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab V Pp d → ∃ (s : SplitPlace D.host.E) (α : Formalism.AUTREP.GAf D.host.E n), Formalism.L2.NG.OverPl Pp s.v ∧ TrivOutside {s.v} α ∧ (∀ γ ∈ GlobalTheory.Hk3.rep V Pp d, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, Formalism.IndefR.principalLevelFrame.pre Ψ γ = k₁ * α * k₂) ∧ ∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ GlobalTheory.Hk3.rep V Pp d ∧ (Formalism.IndefR.principalLevelFrame.pre Ψ γ)⁻¹ * x ∈ Umax D.host.E n := by
  first | exact @GlobalTheory.SplitFrameReps.frame_reps | exact GlobalTheory.SplitFrameReps.frame_reps | (intros; apply GlobalTheory.SplitFrameReps.frame_reps <;> assumption)
