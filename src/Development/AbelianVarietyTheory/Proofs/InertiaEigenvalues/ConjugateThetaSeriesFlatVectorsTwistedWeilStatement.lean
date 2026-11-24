module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.FWTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaSeriesFlatVectorsTwistedWeil
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist

theorem _root_.GlobalTheory.T.conjugate_thetaSeries_flatVectors_twistedWeil : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κw v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κw v₀ O i → PhaseTie T R κw v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (B : Base (Vc D i) (Wc D i)), B.Good → BaseOf R i B → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → FixDat B τ → ∀ (ω ω' : PairRep (Vc D i) (Wc D i)) (ψ ψ' : Twist D Circle) (t t' : T0), B.IsWeil ψ.chi ω → B.IsWeil ψ'.chi ω' → ψ.Good → ψ'.Good → B.admitted ψ.Q → IsTupOf R B ψ t → IsTupOf R B ψ' t' → ConjChar τ ψ ψ' → ∃ ζ : ℂ, IsRoot1 ζ ∧ ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κw i) τ ζ (ph i • series B.F ω (B.vecFlat ψ) h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x))) (ph i • series B.F ω' (B.vecFlat ψ') h (R.ioP i (PiTensorProduct.tprod ℂ u) (c x'))) := by
  first | exact @GlobalTheory.TwistSeriesConj.conj_series_twisted | exact GlobalTheory.TwistSeriesConj.conj_series_twisted | (intros; apply GlobalTheory.TwistSeriesConj.conj_series_twisted <;> assumption)
