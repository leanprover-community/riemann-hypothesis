module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

namespace PI.FinKW

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)

def psiV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F →ₐ[I.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E :=
  (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v) (AlgHom.id I.F I.E)).comp
    (Algebra.TensorProduct.comm I.F I.E (Formalism.MainNotions.S.Af I.F)).toAlgHom

def vecV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    Fin I.n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E :=
  fun i => psiV I v (x i)

def MemLocTo : Prop :=
  ∀ (I : AutInst) (x : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), x ∈ I.Lf →
    ∀ v, vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))

def MemLocFrom : Prop :=
  ∀ (I : AutInst) (x : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F),
    (∀ v, vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) → x ∈ I.Lf

def InjV : Prop :=
  ∀ (I : AutInst) (z : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), (∀ v, psiV I v z = 0) → z = 0

def LiftV : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (y : Fin I.n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E),
    ∃ x : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F, vecV I v x = y ∧ ∀ w, w ≠ v → vecV I w x = 0

end PI.FinKW
