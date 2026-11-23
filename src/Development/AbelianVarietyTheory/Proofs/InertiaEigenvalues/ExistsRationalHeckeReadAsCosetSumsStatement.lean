module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalHeckeReadAsCosetSums
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.DIV Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rationalHecke_read_as_cosetSums : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Formalism.L2.Pj.CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, Formalism.IndefR.FWT.JEvAt T R κ v₀ i (sg0 D A) hV) → Function.Injective ((R.FW i).j (sg0 D A)) → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, GlobalTheory.HeckeSup.ReadsCusp T R κ i (Formalism.IndefR.FWT.res T (sg0 D A)) hV) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R i := by
  first | exact @GlobalTheory.HeckeReadRational.rationalHecke_of_readsCusp | exact GlobalTheory.HeckeReadRational.rationalHecke_of_readsCusp | (intros; apply GlobalTheory.HeckeReadRational.rationalHecke_of_readsCusp <;> assumption)
