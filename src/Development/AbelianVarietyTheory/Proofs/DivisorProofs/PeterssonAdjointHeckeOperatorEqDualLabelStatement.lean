module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonAdjointHeckeOperatorEqDualLabel
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.petersson_adjoint_heckeOperator_eq_dualLabel : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (J : Subgroup (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M (J : Set (GA D V)) χ μ 𝓕 → ∀ P d R R', Hecke₂ V (J : Set (GA D V)) χ Sb P d R → Hecke₂ V (J : Set (GA D V)) χ Sb P (dualLab d) R' → ∀ T ∈ Mult θ M (J : Set (GA D V)) χ, ∀ T' ∈ Mult θ M (J : Set (GA D V)) χ, heckeOn M R T ∈ Mult θ M (J : Set (GA D V)) χ → heckeOn M R' T' ∈ Mult θ M (J : Set (GA D V)) χ → ipM M μ 𝓕 (heckeOn M R T) T' = ipM M μ 𝓕 T (heckeOn M R' T') := by
  first | exact @GlobalTheory.HeckeAdjoint.ipM_heckeOn_dualLab | exact GlobalTheory.HeckeAdjoint.ipM_heckeOn_dualLab | (intros; apply GlobalTheory.HeckeAdjoint.ipM_heckeOn_dualLab <;> assumption)
