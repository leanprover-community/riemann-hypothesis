module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField IsDedekindDomain

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def liftRes (PP : Formalism.L2.DIV.Pl D.host.E) (x : Formalism.L2.DIV.kP PP) : 𝓞 D.host.E :=
  Function.surjInv Ideal.Quotient.mk_surjective x

def supSum {k : Type} [AddCommMonoid k] {r : ℕ} (x : Matrix (Fin r) (Fin r) k) : k :=
  ∑ i : Fin r, if h : i.1 + 1 < r then x i ⟨i.1 + 1, h⟩ else 0

def psiAt (ψ : AddChar (AF D.host.F) ℂ) (e : AE D) (y : D.host.E) : ℂ :=
  ψ (Algebra.trace (AF D.host.F) (AE D) (e * incA D (D.host.xi0 * y)))

def SignsAtG {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : Formalism.IndefR.Links.RealDat D A Ks) (F : Formalism.IndefR.Links.Face D A) : Prop :=
  ∀ (e : R.Pg → AE D), (∀ PP : R.Pg, Formalism.L2.NTheta.IsIdemAt (e PP) PP.1) → ∀ u : F.P0,
    D.what₂.embLL ((F.ψ0 u : D.what₂.LLˣ) : D.what₂.LL) =
      ∏ PP : R.Pg, psiAt R.ψ (e PP)
        ((((Ideal.absNorm PP.1.asIdeal : ℕ) : D.host.E))⁻¹ *
          ((liftRes PP.1 (supSum (((R.eG (u : G)) PP : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP.1)) :
            Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP.1))) : 𝓞 D.host.E) : D.host.E))

end Formalism.IndefR.Mi
