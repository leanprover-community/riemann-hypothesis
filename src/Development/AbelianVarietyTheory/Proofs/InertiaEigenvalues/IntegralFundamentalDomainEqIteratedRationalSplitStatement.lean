module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFundamentalDomainEqIteratedRationalSplit
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift


theorem _root_.GlobalTheory.T.integral_fundamentalDomain_eq_iterated_rationalSplitting : ∀ (D : D7) (r m s t : ℕ) (J : Matrix (Fin r) (Fin s) D.host.E) (K : Matrix (Fin r) (Fin t) D.host.E) (L : Matrix (Fin s) (Fin r) D.host.E) (M : Matrix (Fin t) (Fin r) D.host.E), L * J = 1 → L * K = 0 → M * J = 0 → M * K = 1 → J * L + K * M = 1 → ∀ (μ : Measure (Mx D r m)) (𝓕 : Set (Mx D r m)), IsCovolOne (GlobalTheory.MixModel.ratMx D r m) μ 𝓕 → ∀ (ν : Measure (Mx D s m)) (𝓨 : Set (Mx D s m)), IsCovolOne (GlobalTheory.MixModel.ratMx D s m) ν 𝓨 → ∀ (η : Measure (Mx D t m)) (𝓥 : Set (Mx D t m)), IsCovolOne (GlobalTheory.MixModel.ratMx D t m) η 𝓥 → ∃ κ : ℝ, ∀ T : Mx D r m → ℂ, Continuous T → (∀ γ ∈ GlobalTheory.MixModel.ratMx D r m, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂μ = κ * ∫ v in 𝓥, (∫ y in 𝓨, T (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) ∂ν) ∂η := by
  first | exact @GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated_split | exact GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated_split | (intros; apply GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated_split <;> assumption)
