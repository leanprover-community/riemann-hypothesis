module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.FinZeta (Gv embV VacFin)
open GlobalTheory.AdelicU (frameLat)

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TransferOn (D : D7) (C : HeightOneSpectrum (𝓞 D.host.F) → Prop) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t →
  ∀ v, C v → (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χS w' ∧ GlobalTheory.LFun.UnrAt χT w') →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (U : Submodule ℂ (WO S T → ℂ))
    (hU : ∀ a a', ∀ u ∈ U, om (embV S v a, embV T v a') u ∈ U) (f : U), VacFin ψ S T v f →
  ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Gv S v) X) (x : X) (B : Multiset ℂˣ),
    GlobalTheory.LFun.IsParamVec D.sp.cm.sig S.gram (frameLat S) h ρ x B →
  ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (Gv T v) X') (b : U →ₗ[ℂ] X →ₗ[ℂ] X'),
    (∀ a a' (u : U) y, b ⟨om (embV S v a, embV T v a') u, hU a a' u u.2⟩ (ρ a y) = ρ' a' (b u y)) → b f x ≠ 0 →
    GlobalTheory.LFun.IsParamVec D.sp.cm.sig T.gram (frameLat T) h ρ' (b f x) (stepPar χS χT t (fun _ => B) w)

def CosetSym {G : Type} [Group G] (K : Subgroup G) : Prop :=
  ∀ g : G, Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * g : G) : G ⧸ K)} = Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * g⁻¹ : G) : G ⧸ K)}

end GlobalTheory.ChainOnto

end
