module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
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
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models

theorem rowTest_toCx3 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F h
  obtain ⟨n, ψ, hinj, hrat⟩ := (GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.test_tw_iff (E := R.HE.H) (twAt D.what₂.embLL A3.A.v0) R.emb0 (ι := T0)
    (X := fun t => A3.A.fam.amb.FR t) fun t x => R.Th t (R.jX t x)).2 h
  exact ⟨n, ψ, hinj, fun t i x => hrat t x i⟩

end GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models
