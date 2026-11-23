module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.IndefiniteReal.TensCastR
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabelsFixedByTupleOperatorOfTypeSeries
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.labels_fixed_by_tupleOperator_of_typeSeries : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (C : Submodule ℂ (MMap (R.MY 0))), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ F, ι (D.sEE F) = conjHH X G (j F)) → RowJ R eE X h G t j → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotIn (actM PY (R.MY 0)) C (FinTyp.conjT (rep (D.what₂.ft σ)))) → (∀ σ, ∀ k ∈ X.B.I.Kg X.B.g, ∀ v y, R.HE.e (eE (D.what₂.onb σ)) v (y * kap X h t k) = R.HE.e (eE (D.what₂.onb σ)) v y) → (∀ σ v, ∀ γ ∈ Formalism.L2.Theta.GQ (Yc D 0), ∀ y, R.HE.e (eE (D.what₂.onb σ)) v (γ * y) = R.HE.e (eE (D.what₂.onb σ)) v y) → TypeLab D rep → (∀ σ, D.ntypes.goodTuple (labOf σ)) → LabTie X ι := by
  first | exact @GlobalTheory.LabPinTop.labTie_of_series | exact GlobalTheory.LabPinTop.labTie_of_series | (intros; apply GlobalTheory.LabPinTop.labTie_of_series <;> assumption)
