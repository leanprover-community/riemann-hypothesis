module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTuple
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

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure DivStage (B : Base) (C : Cols B) (W : RowsRest B C) where
  div : DivData B.LL B.Word
  div_good : (∀ v, IsUnit (div.RR.X v).det) ∧ ∀ u v, IsUnit ((div.Nu u).X v).det
  jEE : div.RR.V →ₛₗ[B.embLL] W.EE
  jEE_basis : LinearIndependent ℂ (fun i => jEE (div.RR.b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jEE (div.RR.b i))) = ⊤
  jN : ∀ u, (div.Nu u).V →ₛₗ[B.embLL] W.Mu u
  jN_basis : ∀ u, LinearIndependent ℂ (fun i => jN u ((div.Nu u).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jN u ((div.Nu u).b i))) = ⊤
  Dall_eq : div.Dall = W.Dall
  delP_eq : div.delP = W.delp
  nuIn : ∀ u, (div.Nu u).V →ₗ[B.LL] ((C.fm u).lat 0).V
  nuIn_inj : ∀ u, Function.Injective (nuIn u)
  nuIn_range : ∀ u, LinearMap.range (nuIn u) = (C.fm u).ramSub
  nuIn_jN : ∀ u (x : (div.Nu u).V),
    ((W.eMu u (jN u x) : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) = (C.fm u).emb 0 (nuIn u x)
  nuIn_norm : ∀ u v (x : (div.Nu u).V), Formalism.HermitianLatticesTheory.normAt (div.Nu u).b (div.Nu u).X v x =
    Formalism.HermitianLatticesTheory.normAt ((C.fm u).lat 0).b ((C.fm u).lat 0).X v (nuIn u x)
  jEE_norm : ∀ x : div.RR.V,
    Formalism.HermitianLatticesTheory.normAt div.RR.b div.RR.X (InfinitePlace.mk B.embLL) x = ‖jEE x‖

end GlobalTheory.Mem

end
