module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelBoxProductOrthogonalSumTarget
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_model_box_product_orthogonal_sum_target : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S X T L'' : HSp D) (o'' : OrthDec X T L'') (n Z : Type) [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z] (FS : Frame k S.rank n) (FT : Frame k T.rank Z) (FL : Frame k L''.rank Unit) (FX : Frame k X.rank (Z ⊕ Unit)), FX.β = fromCols (o''.iA.map p.pr * FT.β) (o''.iB.map p.pr * FL.β) → ∀ T₂ TL, p.IsModel ψ FS FT T₂ → p.IsModel ψ FS FL TL → ∀ TX : SB (Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] (WO S X → ℂ), (∀ (a : SB (Matrix Z n k)) (b : SB (Matrix Unit n k)) (Φ : SB (Matrix (Z ⊕ Unit) n k)), (∀ x, Φ.1 x = a.1 x.toRows₁ * b.1 x.toRows₂) → TX Φ = o''.boxT S (T₂ a) (TL b)) → p.IsModel ψ FS FX TX := by
  first | exact @GlobalTheory.LocMod.BoxModel.isModel_boxT | exact GlobalTheory.LocMod.BoxModel.isModel_boxT | (intros; apply GlobalTheory.LocMod.BoxModel.isModel_boxT <;> assumption)
