module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseCoverFramesDifferByRationalIsometry
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.base_cover_frames_differ_by_rational_isometry : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h : GA D (T.V j σ), ∃ γ : GL (Fin D.R.r) D.host.E, (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) ∧ (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) := by
  first | exact @GlobalTheory.CoverFrameMove.frames_differ | exact GlobalTheory.CoverFrameMove.frames_differ | (intros; apply GlobalTheory.CoverFrameMove.frames_differ <;> assumption)
